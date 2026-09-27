/* Small text effects for the deck.
 *
 * .wave: wraps every letter of a [text]{.wave} span in its own <span> with
 * --i set to its position, so CSS like `.wave span { animation-delay:
 * calc(var(--i) * 0.1s) }` can stagger an animation letter by letter.
 * Spaces are left as plain text so lines can still break between words. */
document.addEventListener("DOMContentLoaded", function () {
  document.querySelectorAll(".wave").forEach(function (root) {
    var i = 0;
    var walker = document.createTreeWalker(root, NodeFilter.SHOW_TEXT);
    var texts = [];
    while (walker.nextNode()) texts.push(walker.currentNode);
    texts.forEach(function (node) {
      var frag = document.createDocumentFragment();
      Array.from(node.textContent).forEach(function (ch) {
        if (/\s/.test(ch)) { frag.append(ch); return; }
        var s = document.createElement("span");
        s.textContent = ch;
        s.style.setProperty("--i", i++);
        frag.append(s);
      });
      node.replaceWith(frag);
    });
  });
});
