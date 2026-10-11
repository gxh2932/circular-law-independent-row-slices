# Research page

GitHub Pages serves this static research page at
<https://gxh2932.github.io/circular-law-independent-row-slices/>.
The repository's Pages publishing source is **GitHub Actions**.
[The workflow](../.github/workflows/pages.yml) publishes the HTML, CSS, favicon,
and sitemap, and copies the repository's `paper.pdf` into the same directory.
It runs on changes to the page, PDF, citation metadata, or workflow on `main`,
and can also be run manually. No JavaScript or package installation is needed.

When publishing a new manuscript version, update the visible version, date,
DOI, citation, and scholarly meta tags in `index.html`, together with the root
README and `CITATION.cff`. The deployment copies the current PDF automatically.
Keep `citation_pdf_url` and the PDF in the same public directory.

The HTML has a canonical URL, a descriptive title and description, social
preview metadata, and Google Scholar citation tags. The full author-written
abstract is visible without an account or interactive controls. The sitemap
contains the research page and the PDF; it does not establish indexing.

To use Google Search Console, add the URL-prefix property for the research
page URL. Obtain your own HTML verification tag from Search Console and insert
it into the page's `<head>`, then deploy and complete verification. Submit
`sitemap.xml` and inspect the page URL to request indexing. These steps require
your Google account; this repository does not include a verification token or
claim that Google or Google Scholar has indexed the page.
