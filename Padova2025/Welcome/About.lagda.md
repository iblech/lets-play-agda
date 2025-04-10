# About this project

::: Todo :::
Mention streak, open source dependencies, ...
:::


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

<table id="char-table">
  <tr><th style="text-align: left">Symbol</th><th style="text-align: left">Input method</th></tr>
</table>

<!--
```
module Padova2025.Welcome.About where
```
-->
