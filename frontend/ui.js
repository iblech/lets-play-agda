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
  iframe.src = "/__ttyd/?arg=" + getAgdaModuleName() + "&arg=" + encodeURIComponent(id);

  // xterm.js has issues if the font is not available at initialization time,
  // hence ensure that it is available before the frame contents are loaded
  /*
  new FontFace('JuliaMono', 'local("JuliaMono"), local("JuliaMono Regular"), url(./juliamono.woff2)').load().then(function (f) {
    iframe.contentDocument.fonts.add(f);
    iframe.src = "/__ttyd/?arg=" + getAgdaModuleName() + "&arg=" + encodeURIComponent(id);
  });
  */

  iframe.onload = function () {
    iframe.contentWindow.document.addEventListener('keydown', function (e) {
      if(e.altKey && e.keyCode == 13) {
        if(document.fullscreenElement) {
          document.exitFullscreen();
        } else {
          iframe.requestFullscreen();
        }
      }

      // For reasons regarding terminal standard, xterm.js cannot forward a couple of
      // events with Ctrl pressed to the application. As a workaround, reraise those
      // events without Ctrl pressed, and have Emacs accept those new shortcuts.
      if(e.ctrlKey && (e.key == ',' || e.key == '.' || e.key == '=' || e.key == ';')) {
        iframe.contentWindow.document.getElementsByClassName("xterm-helper-textarea")[0].dispatchEvent(
          new KeyboardEvent('keydown', {
            'key':     e.key,
            'code':    e.code,
            'keyCode': e.keyCode,
            'which':   e.which
          })
        );
      }
    }, true);

    new MutationObserver(function(mutations) {
      if(iframe.contentDocument.title.includes("SUCCESS")) {
        const encodedPayload = iframe.contentDocument.title.split(' ')[1];
        const decodedPayload = decodeURIComponent(atob(encodedPayload).split('').map((c) => '%' + ('00' + c.charCodeAt(0).toString(16)).slice(-2)).join(''));
        recordActivity();
        recordCode(getAgdaModuleName(), id, decodedPayload);
        updateCode(iframe, id);
        localStorage.setItem(getAgdaModuleName() + "/" + id + "/success", "true");
        renderToc();
        printActivity();
        attachReferenceSolution(iframe, id);
        showConfetti();
        window.setTimeout(confetti.stop, 1000);
      }
    }).observe(
      iframe.contentDocument.querySelector('title'),
      { subtree: true, characterData: true, childList: true }
    );

    window.setTimeout(function () {
      iframe.style.display = "block";
      block.remove();
    }, 100);

    let sheet = iframe.contentWindow.document.styleSheets[0];
    sheet.insertRule('.xterm-viewport { overflow-y: hidden !important; }', sheet.cssRules.length);
  };

  return iframe;
}

function attachEditor(block) {
  block.classList.add("exercise");
  const id = block.innerText.split(/\s+/)[0];

  updateCode(block, id);

  for(const holeMarker of block.getElementsByClassName("Hole")) {
    const editButton = document.createElement("a");
    editButton.className = "edit";
    editButton.innerHTML = "🐔 Edit hole…";
    editButton.onclick = function () {
      editButton.onclick = null;
      editButton.innerHTML = "⏳ Please wait…";
      block.classList.add("spinning");
      block.insertAdjacentElement("afterend", createIframe(block, id));
      recordActivity();
      printActivity();
    };
    holeMarker.insertAdjacentElement("afterend", editButton);

    if(location.href.includes("localhost") || location.href.includes("solutions") || getCode(getAgdaModuleName(), id) !== null) {
      attachReferenceSolution(editButton, id);
    }
  }
}

function attachReferenceSolution(block, id) {
  const solution = document.getElementById("reference-solution-" + id);
  if(solution === null) return;
  solution.removeAttribute("id");  // Don't show button when solving an exercise a second time

  const showButton = document.createElement("a");
  showButton.className = "show-reference-solution";
  showButton.innerHTML = "🧑‍🏫 Show reference solution…";
  showButton.onclick = function () {
    if(
      getCode(getAgdaModuleName(), id) !== null ||
      location.href.includes("localhost")       ||
      location.href.includes("solutions")       ||
      window.confirm("Please confirm that you would like to peek at the reference solution.")
    ) {
      showButton.after(solution);
      showButton.remove();
    }
  };

  block.insertAdjacentElement("afterend", showButton);
}

function updateCode(block, id) {
  const code = getCode(getAgdaModuleName(), id);

  const old = document.getElementById("solution-" + id);
  if(old !== null) {
    old.remove();
  }

  if(code !== null) {
    const pre = document.createElement("pre");
    pre.classList.add("solution");
    pre.id = "solution-" + id;
    pre.innerText = code;

    const a = document.createElement("a");
    a.setAttribute("href", "javascript:downloadLocalStorage()");
    a.classList.add("download-backup");
    const span = document.createElement("span");
    span.appendChild(document.createTextNode("📥"));
    a.appendChild(span);
    a.appendChild(document.createTextNode(" Download backup of this and your other solutions…"));
    pre.appendChild(a);

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

function getActivityLog(str) {
  const log = str === undefined ? localStorage.getItem("activityLog") : str;

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

function activateHintsAndMore() {
  activateDetails("Hint", "show-hint", "👉 Show hint…");
  activateDetails("More", "show-more", "👉 Show more…");
}

function activateDetails(elemClass, popupClass, action) {
  for(const elem of document.getElementsByClassName(elemClass)) {
    for(const li of elem.getElementsByTagName("li")) {
      activateSpoiler(li);
    }

    elem.style.display = "none";
    const showButton = document.createElement("a");
    showButton.className = popupClass;
    showButton.innerHTML = action;
    showButton.onclick = function () {
      showButton.remove();
      elem.style.display = "block";
    };
    elem.insertAdjacentElement("afterend", showButton);
  }
}

function activateSpoiler(obj) {
  let st = true;
  obj.style.cursor = "pointer";
  obj.onclick = function () {
    if(st) {
      obj.classList.add("spoiler");
    } else {
      obj.classList.remove("spoiler");
    }
    st = ! st;
  };
  obj.onclick();
}

function renderToc() {
  const list = document.getElementsByTagName("nav")[0].getElementsByTagName("ol")[0];

  for(const link of list.getElementsByTagName("a")) {
    const file  = getAgdaModuleName(link.href);
    const stats = getCompletionStatus(file);
    link.parentElement.classList.add(stats);
  }
}

// Code for setting up the dictionary "characterDescriptions" is generated by
// the build system and prepended to this source file
function attachTooltips() {
  const a = new Date();
  for(const link of document.getElementsByTagName("a")) {
    const d = characterDescriptions[link.innerText];
    if(d !== undefined) {
      link.title = "Input method in Emacs:\n" + d;
    }
  }
}

function downloadLocalStorage() {
  const a = document.createElement("a");
  const blob = new Blob([JSON.stringify(localStorage)], {type: "application/json"});
  const url = URL.createObjectURL(blob);
  a.setAttribute("href", url);
  a.setAttribute("download", "lets-play-agda-" + Math.floor(new Date().getTime() / 1000) + ".json");
  a.click();
}

function importIntoLocalStorage() {
  const input = document.createElement("input");
  input.type = "file";
  input.accept = ".json";

  input.onchange = () => {
    const file = input.files[0];
    if (!file) {
      alert("No file selected.");
      return;
    }

    const reader = new FileReader();
    reader.onload = () => {
      try {
        const json = JSON.parse(reader.result);

        let numImports = 0;
        for(const key in json) {
          if(key == "activityLog") {
            const oldLog  = localStorage.getItem("activityLog");
            const moments = new Set(getActivityLog(json["activityLog"]).concat(getActivityLog()));
            putActivityLog([...new Set(moments)].sort((a, b) => a - b));
            const newLog = localStorage.getItem("activityLog");
            if(oldLog != newLog) {
              numImports++;
            }
          } else {
            const oldValue = localStorage.getItem(key);
            localStorage.setItem(key, json[key]);
            const newValue = localStorage.getItem(key);
            if(oldValue != newValue) {
              numImports++;
            }
          }
        }

        if(numImports > 0) {
          alert("Successfully imported " + numImports + " records.");
          renderToc();
          printActivity();
        } else {
          alert("The file's contents were already part of the local storage.");
        }
      } catch (err) {
        alert("Couldn't parse file; is it really a backup file generated by this site?\n\n" + err);
      }
    };

    reader.readAsText(file);
  };

  input.click();
}

function showConfetti() {
  confetti.start();
  window.setTimeout(confetti.stop, 1000);
}

attachEditors();
activateHintsAndMore();
printActivity();
renderToc();
attachTooltips();
