# About this project

## Credits

::: Todo :::
Acknowledge participants at the Chaos Communication Congress, ALGAR summer
school, Proof and Computation etc. and of course in Padova
:::

Pull requests were contributed by:

- Matteo Cusin


### Open source dependencies

This interactive Agda tutorial builds on awesome free software projects:

<div class="logos">
<a href="https://www.linux.org/"><img src="images/linux.svg" alt="Linux"></a>
<a href="https://www.gnu.org/"><img src="images/gnu.svg" alt="GNU"></a>
<a href="https://perl.org/"><img src="images/perl.svg" alt="Perl"></a>
<a href="https://nixos.org/"><img src="images/nixos.svg" alt="NixOS"></a>
<a href="https://nginx.org/"><img src="images/nginx.svg" alt="nginx"></a>
<a href="https://xtermjs.org/"><img src="images/xtermjs.svg" alt="xterm.js"></a>
<a href="https://github.com/tsl0922/ttyd"><img src="images/ttyd.svg" alt="ttyd"></a>
<a href="https://github.com/containers/bubblewrap"><img src="images/bubblewrap.svg" alt="bubblewrap"></a>
</div>

The [confetti animation](javascript:showConfetti()) is by
[Elias Ruiz Monserrat](https://gist.github.com/elrumo/3055a9163fd2d0d19f323db744b0a094).


### Similar projects for other languages

- [Holbert](https://liamoc.net/holbert/)
- [Lean Game Server](https://adam.math.hhu.de/)
- [Rocq interactive online system](https://coq.vercel.app/)


## Working locally

In case you prefer to work with a local Agda installation, there is an
[archive](Padova2025.zip) of all Agda code.

[It is also possible to self-host Let's play Agda.](https://github.com/iblech/lets-play-agda/)


## Backing up your data

- For the interactive Agda elements of this project, you are connected to an
  container including Agda running on a server of mine. This container is ephemeral,
  your Agda code is not permanently stored on the server.

- Instead, your solutions to Agda exercises are only stored in your browser's local
  storage. This storage is in principle permanent but in practice prone to be
  cleared, for instance when working in your browser's private mode or when
  deleting "application data" of web sites. Hence you might want to
  periodically [download your solutions](javascript:downloadLocalStorage()) for safekeeping.

- You can [import backups by clicking here](javascript:importIntoLocalStorage()).
  This will merge the backup's contents with the local storage.


## Streak

As soon as you have started filling in your first hole, a small calendar will
appear in the lower left corner below the navigation. This calender allows you
to monitor your progress. Like your Agda code, this activity log is only stored
in your browser's local storage.

<span class="daybox active"></span> Days on which you have been playing<br>
<span class="daybox resting"></span> Days on which you have been resting<br>
<span class="daybox inactive"></span> Days on which you have been inactive

To better match night owls, a day is defined as ending at 5 am in the morning.
For the case that this is useful to you, also your longest streak of continuous
day-after-day activity is computed. Up two resting days in each 7-day time span
do not interrupt a streak.


## Unicode symbols

Agda's community is big on Unicode, helping us to notationally mimic
blackboard mathematics. On this webpage, you can hover over special symbols in
Agda fragments to learn how they can be input. Many LaTeX commands work, for
instance `\alpha` will produce a Greek `α`.

Here is a list of Unicode symbols used in this course.


<script>
  window.onload = function () {
    let table = document.getElementById("char-table");

    for(const symbol of Object.keys(characterDescriptions).toSorted()) {
      const tr = document.createElement("tr");

      const td1 = document.createElement("td");
      td1.appendChild(document.createTextNode(symbol));

      const td2  = document.createElement("td");
      const code = document.createElement("code");
      code.appendChild(document.createTextNode(characterDescriptions[symbol]));
      td2.appendChild(code);

      tr.appendChild(td1);
      tr.appendChild(td2);
      table.appendChild(tr);
    }
  };
</script>

<div style="column-count: 2"><table id="char-table">
</table></div>

<!--
```
module Padova2025.Welcome.About where
```
-->
