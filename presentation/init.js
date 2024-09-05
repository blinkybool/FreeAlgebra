// utility function that excepts a fragmentshown or fragmenthidden event and returns a boolean indicating whether or not
// the fragment is a video
const isVideoFragment = (event) => event.fragment.nodeName === 'VIDEO';

// Listens for the 'fragmentshown' event; if the fragment being shown is a video, play the video
Reveal.addEventListener('fragmentshown', (event) => {
if (isVideoFragment(event)) {
  event.fragment.play();
}
});

// Listens for the 'fragmenthidden' event; if the fragment being hidden is a video, pause the video
Reveal.addEventListener('fragmenthidden', (event) => {
if (isVideoFragment(event)) {
  event.fragment.pause();
}
});

Reveal.initialize({
  scale: 0.5,
  customcontrols: {
    controls: [
      { icon: '<i class="fa fa-pen-square"></i>',
        title: 'Toggle chalkboard (B)',
        action: 'RevealChalkboard.toggleChalkboard();'
      },
      { icon: '<i class="fa fa-pen"></i>',
        title: 'Toggle notes canvas (C)',
        action: 'RevealChalkboard.toggleNotesCanvas();'
      }
    ]
  },
  transition: "fade",

  katex: {
    macros: {
      "\\R": "\\mathbb{R}",
      "\\cat": "\\mathcal{#1}",
      "\\Fun": "\\mathrm{Fun}",
      "\\Id": "\\mathrm{Id}",
    },
  },

  plugins: [RevealMath.KaTeX],
  history: true,
});