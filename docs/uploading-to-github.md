# Uploading this project to GitHub

You can publish this project while parts of the proof remain unfinished.
Keep its scope statement, numerical evidence and attribution with the code.

## Using GitHub Desktop

GitHub Desktop provides a graphical way to create, commit and publish a
repository. It is free. See GitHub's
[first-repository guide](https://docs.github.com/en/desktop/overview/creating-your-first-repository-using-github-desktop).

1. Unzip the supplied archive. Inside is a `prime-gaps-lean` folder containing
   `README.md`, `formal`, `docs`, and the other project files.
2. Install GitHub Desktop and sign in as `romyar1`.
3. In GitHub Desktop, create a new local repository named `prime-gaps-lean`
   in a separate empty location. The archive supplies its own README,
   ignore rules and existing license notices; additional starter files are
   unnecessary.
4. Copy the **contents** of the extracted folder into that new repository
   folder. Include the hidden `.github` folder and `.gitignore` file. On a
   Mac, Command–Shift–period toggles hidden files in Finder.
5. Review the files in GitHub Desktop, enter a summary such as
   `Add conditional prime-gap formalization and numerical evidence`, and
   click the **Commit** button.
6. Click **Publish repository**, use your personal account, and clear
   **Keep this code private** to make it public. GitHub's
   [publishing instructions](https://docs.github.com/en/desktop/adding-and-cloning-repositories/adding-an-existing-project-to-github-using-github-desktop)
   describe these controls.

If that repository name is already in use, choose another name or add these
files to the existing repository you intend to use. After publication, the
repository's Actions tab will show the first hosted verification attempt.
The package includes the result of its local audit; a successful hosted run
is a separate check.

## Browser uploads

The GitHub website also accepts folders and files, but it permits at most
100 files in one upload and 25 MiB per file. This project has hundreds of
source files, so GitHub Desktop avoids repeated upload batches. See the
[official upload guide](https://docs.github.com/en/repositories/working-with-files/managing-files/adding-a-file-to-a-repository).

Publish the extracted source tree. Keeping only the ZIP as a repository file
would prevent GitHub from displaying the individual sources and running the
included workflow.

## What to share

The archive already selects the checked Lean sources, pinned configuration,
documentation, saved numerical evidence and existing notices. It excludes
dependency caches, compiled Lean objects, unfinished scratch files and local
Git history.

The numerical records belong in the repository even though their connection
to the 262 integral premises is not yet formalized. They are explicitly
labelled computational evidence. Later commits can add the missing numerical
programs and Lean proofs without changing what this initial snapshot claims.
