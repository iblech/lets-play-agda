# About this project

::: Todo :::
Mention streak...
:::


## Credits

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


## Download

In case you prefer to work with a local Agda installation, there is an
[archive](Padova2025.zip) of all Agda code.


## Unicode symbols

Agda's community is big on Unicode, helping us to notationally mimic
blackboard mathematics. On this webpage, you can hover over special symbols in
Agda fragments to learn how they can be input. Many LaTeX commands work, for
instance `\alpha` will produce a Greek `α`.

Here is a list of Unicode symbols used in this course.


<script id="char-loader">
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
