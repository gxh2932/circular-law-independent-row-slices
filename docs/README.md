# Research page

GitHub Pages serves this static research page at
<https://gxh2932.github.io/circular-law-independent-row-slices/>.
The repository's Pages publishing source is **GitHub Actions**.
[The workflow](../.github/workflows/pages.yml) publishes the HTML, CSS, favicon,
and both sitemap formats, and copies the repository's `paper.pdf` into the same directory.
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

The page includes a Google Search Console HTML verification tag for the
research page's URL-prefix property. Keep that tag in the published `<head>`:
Google periodically checks it to confirm ownership. Sign in with the Google
account that registered the property to inspect indexing and search performance.
If another owner needs a verification tag, add it without removing the existing
tag. The XML sitemap is `sitemap.xml`; `sitemap.txt` provides the same two URLs
in Google's supported plain-text format. Keep the URL lists in both files in
sync. The text version provides an alternative endpoint when troubleshooting
Search Console fetch failures; its submission alone does not confirm that a
fetch problem has been resolved. URL Inspection can request indexing for the
research page and PDF. Verification and submission do not establish that Google
or Google Scholar has indexed either URL.
