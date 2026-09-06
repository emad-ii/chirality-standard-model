# Illustration and film notes

The website uses original stylised illustrations generated with the built-in image-generation tool, alongside mathematical diagrams drawn from the repository data. The palette is midnight navy, faded blue, copper and ivory; the texture combines engraved ink, gouache and paper grain. Portraits are interpretations, not photographs or depictions of a historical meeting.

Only the optimised WebP delivery images are included in the website. Image conversion changes the file format, not the composition.

## Attribution

The Wu illustration adapts [Informal portrait of Chien-shiung Wu](https://commons.wikimedia.org/wiki/File:Informal_portrait_of_Chien-shiung_Wu.jpg), AIP Emilio Segrè Visual Archives, Segrè Collection, Wu Chien-shiung B8. [Archive record](https://repository.aip.org/node/71456). The source is licensed [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). The adaptation changes the medium, colour, background and composition.

The remaining historical portraits use the generated Wu illustration as a style reference only. They do not reproduce a downloaded historical photograph. Names, dates and scientific claims have separate references in the essay.

## Exact generation prompts

### wu

Output: `public/wu-illustration.webp`.

Use case: style-transfer. Asset type: editorial illustration for a public-facing physics essay, portrait format. Reference image: the supplied archival portrait of Chien-Shiung Wu, identity reference only. Create a beautifully stylised ink-and-gouache illustration of Wu, retaining her recognisable face, swept dark hair and composed expression, now seated beside a simplified 1950s beta-decay laboratory bench. This is clearly an illustrated historical interpretation, not a photograph or exact reconstruction of an apparatus. Medium: fine engraved ink contours, sparse screen-printed shapes, subtle handmade paper grain, sophisticated science-book illustration. Palette: midnight navy #080b10, muted powder blue, warm ivory and a little copper orange, matching a dark editorial website. Frame waist-up with breathing room around the face, lab background gently abstracted with a coil and instrument dial; no equations, no text, no watermark, no photographic rendering. Preserve dignified scientific character. Make the result striking but restrained, with crisp shapes that read at small web sizes.

### lie

Output: `public/lie-illustration.webp`.

Use case: illustration-story. Asset type: portrait illustration in a unified historical gallery for a physics website. Input image is STYLE REFERENCE ONLY, not the subject. Match its engraved ink lines, ivory handmade paper, midnight-navy shadows, faded blue screenprint shapes and very restrained copper details precisely. New subject: Sophus Lie, the Norwegian mathematician in later life: round spectacles, short parted hair, a long full beard and a formal nineteenth-century jacket. A few restrained circular construction lines behind him suggest continuous rotations. Compose a dignified, recognisable head-and-shoulders illustrated portrait, 4:5 vertical crop, centre the face with ample space around the hair and beard. Use the same paper texture, rendering complexity and colour balance as the reference of Wu. Clearly a stylised interpretation, not a photograph. No readable text, no equations, no name labels, no watermark, no invented awards or modern accessories. Do not reproduce Wu's face.

### killing

Output: `public/killing-illustration.webp`.

Use case: illustration-story. Asset type: portrait illustration in a unified historical gallery for a physics website. Input image is STYLE REFERENCE ONLY, not the subject. Match its engraved ink lines, ivory handmade paper, midnight-navy shadows, faded blue screenprint shapes and very restrained copper details precisely. New subject: Wilhelm Killing, the German mathematician in later life: a high bald forehead with hair at the sides, very large full dark beard, a formal late-nineteenth-century jacket and a three-quarter pose. A spare geometric branching sketch in the background suggests the classification of symmetry. Compose a dignified, recognisable head-and-shoulders illustrated portrait, 4:5 vertical crop, centre the face with ample space around the hair and beard. Use the same paper texture, rendering complexity and colour balance as the reference of Wu. Clearly a stylised interpretation, not a photograph. No readable text, no equations, no name labels, no watermark, no invented awards or modern accessories. Do not reproduce Wu's face.

### cartan

Output: `public/cartan-illustration.webp`.

Use case: illustration-story. Asset type: portrait illustration in a unified historical gallery for a physics website. Input image is STYLE REFERENCE ONLY, not the subject. Match its engraved ink lines, ivory handmade paper, midnight-navy shadows, faded blue screenprint shapes and very restrained copper details precisely. New subject: Élie Cartan, the French mathematician around the early twentieth century: spectacles, side-parted dark hair, prominent moustache and pointed beard, formal jacket and vest. A few fine connected geometric nodes in the background suggest the classification of Lie algebras. Compose a dignified, recognisable head-and-shoulders illustrated portrait, 4:5 vertical crop, centre the face with ample space around the hair and beard. Use the same paper texture, rendering complexity and colour balance as the reference of Wu. Clearly a stylised interpretation, not a photograph. No readable text, no equations, no name labels, no watermark, no invented awards or modern accessories. Do not reproduce Wu's face.

### electroweak

Output: `public/electroweak-illustration.webp`.

Use case: illustration-story. Website historical gallery asset. Use the reference ONLY for the visual style. A horizontal triptych of exactly three equally sized, clearly separate head-and-shoulder portraits on the same paper: from left to right Sheldon Glashow (short white hair, roundish spectacles, clean shaven, suit), Steven Weinberg (receding grey hair, broad forehead, clean shaven, no glasses, suit), Abdus Salam (swept-back thinning grey hair, dark framed glasses, full grey beard, suit). Recognisable later-life likenesses, not a historical meeting. No one else. Match the reference's finely engraved ink, warm ivory paper grain, midnight-navy shadows, muted powder-blue screenprinted shapes and tiny copper geometric accents. Wide composition, all faces same scale, dignified and calm, no text or labels, no equations, no watermark, not photorealistic. Keep the subjects separated by a little quiet paper space without heavy panel borders. They should look like plates from the same beautifully illustrated science book as the Wu reference, not generic AI paintings.

### unification

Output: `public/unification-illustration.webp`.

Use case: illustration-story. Website historical gallery asset. Use the reference ONLY for the visual style. A horizontal diptych of exactly two equally sized, clearly separate head-and-shoulder portraits on the same paper: Howard Georgi at left (straight grey fringe, low-set glasses, long white beard, warm smile) and Sheldon Glashow at right (short white hair, spectacles, clean shaven, suit). Recognisable later-life likenesses, not a historical meeting. No one else. Match the reference's finely engraved ink, warm ivory paper grain, midnight-navy shadows, muted powder-blue screenprinted shapes and tiny copper geometric accents. Wide composition, all faces same scale, dignified and calm, no text or labels, no equations, no watermark, not photorealistic. Keep the subjects separated by a little quiet paper space without heavy panel borders. They should look like plates from the same beautifully illustrated science book as the Wu reference, not generic AI paintings.

### Continuous symmetry

Output: `public/symmetry-illustration.webp`.

Use case: stylized-concept. Asset type: wide editorial section illustration for an accessible physics essay about Lie groups, not a chart. Create an exquisite ink, engraving and gouache illustration of the idea of continuous symmetry: a luminous ivory sphere suspended over an open nineteenth-century mathematics notebook, with a brass compass and finely drawn circular rotation paths. On the facing page, a small branching geometric sketch suggests how simple local motions describe a larger symmetry. Palette midnight navy, faded blue, ivory paper and restrained copper, subtle screenprint grain. Composition landscape 3:2, sphere upper centre, notebook along lower third, generous dark negative space around the circular paths. Rich tactile detail, quietly beautiful, designed to belong beside a stylised archival scientific portrait. No readable writing, no mathematical equations, no labels, no watermark, no neon sci-fi, no photorealism. This is a conceptual illustration; do not imitate a historical document.

## Mathematical exhibits

D3 animates the scroll-driven candidate display and an explicitly qualitative parity illustration. Root coordinates and intersections are derived from the bundled E6 certificate. Three.js renders a linear 3D projection, with 72 distinct positions checked by the data test. These images are mathematical projections, not particle positions.

## Equation film

`../media/equations/equation_story.py` is the editable Manim Community 0.20.1 source. The 1080p, 24fps film runs for approximately 82 seconds and is copied to `public/equation-story.mp4` when the site builds. It has no audio track. Captions and an HTML transcript provide the accompanying explanation. The poster, candidate-selection frame and final family-count frame were inspected after rendering.
