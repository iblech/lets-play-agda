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
    window.setTimeout(function () {
      iframe.style.display = "block";
      block.remove();
      iframe.focus();
    }, 100);
  };
  iframe.src = "/__ttyd/?arg=" + (new URL(location.href).pathname.split(".html")[0].split("/").pop()) + "&arg=" + id;
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
}

function attachEditors() {
  for(const block of document.getElementsByTagName("pre")) {
    if(block.innerHTML.indexOf("{!!}") >= 0) {
      attachEditor(block);
    }
  }
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
    console.log(currentRestingFifths);

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

attachEditors();
activateHints();
printActivity();
