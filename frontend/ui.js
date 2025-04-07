function getAgdaModuleName(url) {
  if(url === undefined) {
    url = location.href;
  }

  return new URL(url).pathname.split(".html")[0].split("/").pop();
}

function recordCode(file, id, code) {
  localStorage.setItem(file + "/code/" + id, code);
}

function getCode(file, id) {
  return localStorage.getItem(file + "/code/" + id);
}

function getCompletionStatus(file) {
  const idsString = localStorage.getItem(file + "/ids");
  if(idsString === null) return "status-0";

  const ids   = idsString.split(",").filter(e => e);
  let   found = 0;
  for(const id of ids) {
    if(localStorage.getItem(file + "/" + id + "/success")) {
      found++;
    }
  }

  if(found == ids.length) {
    return "status-2";
  } else if(found > 0) {
    return "status-1";
  } else {
    return "status-0";
  }
}

function createIframe(block, id) {
  const iframe = document.createElement("iframe");

  iframe.onload = function () {
    let sheet = iframe.contentWindow.document.styleSheets[0];
    sheet.insertRule('.xterm-viewport { overflow-y: hidden !important; }', sheet.cssRules.length);

    // XXX: This font loading will likely come too late
    new FontFace('JuliaMono', 'local("JuliaMono"), local("JuliaMono Regular"), url(./juliamono.woff2)').load().then(function (f) {
      iframe.contentDocument.fonts.add(f);
    });

    iframe.contentWindow.document.addEventListener('keydown', function (e) {
      if(e.altKey && e.keyCode == 13) {
        if(document.fullscreenElement) {
          document.exitFullscreen();
        } else {
          iframe.requestFullscreen();
        }
      }
    }, true);

    new MutationObserver(function(mutations) {
      if(iframe.contentDocument.title.includes("SUCCESS")) {
        const encodedPayload = iframe.contentDocument.title.split(' ')[1];
        const decodedPayload = decodeURIComponent(atob(encodedPayload).split('').map((c) => '%' + ('00' + c.charCodeAt(0).toString(16)).slice(-2)).join(''));
        recordCode(getAgdaModuleName(), id, decodedPayload);
        updateCode(iframe, id);
        localStorage.setItem(getAgdaModuleName() + "/" + id + "/success", "true");
        renderToc();
        confetti.start();
        window.setTimeout(confetti.stop, 1000);
      }
    }).observe(
      iframe.contentDocument.querySelector('title'),
      { subtree: true, characterData: true, childList: true }
    );

    window.setTimeout(function () {
      iframe.style.display = "block";
      block.remove();
      iframe.focus();
    }, 100);
  };
  iframe.src = "/__ttyd/?arg=" + getAgdaModuleName() + "&arg=" + id;
  return iframe;
}

function attachEditor(block) {
  block.classList.add("exercise");
  const id = block.innerText.split(/\s+/)[0];

  for(const holeMarker of block.getElementsByClassName("Hole")) {
    const editButton = document.createElement("a");
    editButton.className = "edit";
    editButton.innerHTML = "🐔 Edit hole…";
    editButton.onclick = function () {
      block.classList.add("spinning");
      block.insertAdjacentElement("afterend", createIframe(block, id));
      recordActivity();
      printActivity();
    };
    holeMarker.insertAdjacentElement("afterend", editButton);
  }

  updateCode(block, id);
}

function updateCode(block, id) {
  const code = getCode(getAgdaModuleName(), id);

  const old = document.getElementById("solution-" + id);
  if(old !== null) {
    old.remove();
    console.log("removed");
  }

  if(code !== null) {
    console.log(code);
    const pre = document.createElement("pre");
    pre.id = "solution-" + id;
    pre.innerText = code;
    pre.classList.add("solution");
    block.insertAdjacentElement("afterend", pre);
  }
}

function attachEditors() {
  let ids = [];

  for(const block of document.getElementsByTagName("pre")) {
    if(block.innerHTML.indexOf("{!!}") >= 0) {
      const id = block.innerText.split(/\s+/)[0];
      ids.push(id);
      attachEditor(block);
    }
  }

  localStorage.setItem(getAgdaModuleName() + "/" + "ids", ids.join(","));
}

function getActivityLog() {
  const log = localStorage.getItem("activityLog");

  if(log === null) {
    return [];
  } else {
    return log.split(",").map((x) => Number(x));
  }
}

function putActivityLog(log) {
  if(log.length >= 1) {
    localStorage.setItem("activityLog", log.join(","));
  } else {
    localStorage.removeItem("activityLog");
  }
}

function getToday() {
  const today = new Date();

  // regard 5am as the start and end of a day, so that the streak is properly
  // detected for night owls
  today.setHours(today.getHours() - 5);

  // canonicalize
  today.setHours(0,0,0,0);

  return today;
}

function recordActivity() {
  const log = getActivityLog();
  const today = getToday();

  if(log.length == 0 || log[log.length-1] < today.getTime()) {
    log.push(today.getTime());
  }

  putActivityLog(log);
}

function createDayBox(day, active) {
  const box = document.createElement("div");
  box.classList.add("daybox");
  box.classList.add(active);
  box.title = day.toDateString();
  return box;
}

function formatStreakLength(typ, len) {
  const tr = document.createElement("tr");

  {
    const td = document.createElement("td");
    td.appendChild(document.createTextNode(typ + " streak:"));
    tr.appendChild(td);
  }

  {
    const td = document.createElement("td");
    td.appendChild(document.createTextNode(len + " " + (len == 1 ? "day" : "days")));
    tr.appendChild(td);
  }

  return tr;
}

function printActivity() {
  const div   = document.getElementById("activity");
  const log   = getActivityLog();
  const today = getToday();
  const cur   = log.length > 0 ? new Date(log[0]) : getToday();

  div.replaceChildren();

  if(log.length == 0) {
    return;
  }

  const boxes = document.createElement("div");
  boxes.style.lineHeight = "0.5em";

  // Scroll back to the beginning of the current month...
  cur.setDate(1);
  // ...and then to the first preceding Monday
  while(cur.getDay() != 1) {
    cur.setDate(cur.getDate() - 1);
  }

  // We maintain the current streak iff among the last seven days there have
  // been at most two resting days. To this end, we maintain a variable
  // currestRestingFifths. Every active day contributes two fifths, such that
  // five active days fully replenish the resting reservoir.
  const allowedRestingDays = 2;
  let currentStreak        = 0;
  let currentRestingFifths = allowedRestingDays * 5;
  let inStreak             = false;
  let maxStreak            = 0;
  let i                    = 0;

  while(cur <= today) {
    let hadActivity = log[0] == cur.getTime();
    let displayActivity;
    if(hadActivity) {
      log.shift();
      displayActivity = "active";
      inStreak = true;
      currentRestingFifths += 2;
    } else {
      displayActivity = "inactive";
    }

    if(inStreak && !hadActivity && currentRestingFifths >= 5) {
      currentRestingFifths -= 5;
      hadActivity = true;
      displayActivity = "resting";
    }

    boxes.appendChild(createDayBox(cur, displayActivity));

    if(hadActivity) {
      currentStreak++;
      if(currentStreak > maxStreak) {
        maxStreak = currentStreak;
      }
    } else {
      currentRestingFifths = allowedRestingDays * 5;
      currentStreak       = 0;
      inStreak            = false;
    }

    if(currentRestingFifths > allowedRestingDays * 5) {
      currentRestingFifths = allowedRestingDays * 5;
    }

    cur.setDate(cur.getDate() + 1);

    i++;
    if(i == 7) {
      boxes.appendChild(document.createElement("br"));
      i = 0;
    }
  }

  const table = document.createElement("table");
  table.appendChild(formatStreakLength("Current", currentStreak));
  table.appendChild(formatStreakLength("Longest", maxStreak));
  div.appendChild(table);
  div.appendChild(boxes);
}

function activateHints() {
  for(const hint of document.getElementsByClassName("Hint")) {
    let st = true;
    hint.onclick = function () {
      if(st) {
        hint.classList.add("spoiler");
      } else {
        hint.classList.remove("spoiler");
      }
      st = ! st;
    };
  }
}

function renderToc() {
  const list = document.getElementsByTagName("nav")[0].getElementsByTagName("ol")[0];

  for(const link of list.getElementsByTagName("a")) {
    const file  = getAgdaModuleName(link.href);
    const stats = getCompletionStatus(file);
    link.parentElement.classList.add(stats);
  }
}

attachEditors();
activateHints();
printActivity();
renderToc();
