import           Development.Shake
import           Development.Shake.Command
import           Development.Shake.FilePath
import           Development.Shake.Util

dist :: FilePath
dist = "dist"

main :: IO ()
main = shakeArgs shakeOptions $ do
    want [dist </> "thesis.pdf", dist </> "thesis.tex", "thesis.lhs"]

    phony "clean" $ do
      putNormal "Remove dist"
      cmd_ "rm" "-r" "-f" dist

    phony "clean-aux" $ do
      putNormal "Remove *.aux"
      cmd_ "rm" (dist </> "*.aux")

    let content = "content"
        chapter = "chapter"

    "dist/thesis.tex" %> \out -> do
      cmd_ "lhs2tex" "thesis.lhs" "-o" out

    "dist/thesis.bib" %> \out -> do
      cmd_ "cp" "thesis.bib" out
      cmd_ "sh -c" ["cd dist; bibtex thesis"]

    "thesis.bib" %> \out -> do
      need [dist </> out]
      cmd_ "touch" (dist </> "thesis.tex")

    "//*.lhs" %> \_ -> cmd_ "touch" (dist </> "thesis.tex")
    "//*.lcurry" %> \_ -> cmd_ "touch" (dist </> "thesis.tex")
    "content/*.tex" %> \_ -> cmd_ "touch" (dist </> "thesis.tex")
    "setup.tex" %> \_ -> cmd_ "touch" (dist </> "thesis.tex")
    "content/figures/*.tex" %> \_ -> cmd_ "touch" (dist </> "thesis.tex")

--    "content/chapter/*.lcurry" %> \out -> do
--      cmd_ "lhs2tex" out "-o" (out -<.> "tex")

    "content/chapter/*.v" %> \out -> do
      let fileName = takeFileName out
      cmd_ "coqdoc" fileName "--latex" "--no-preamble" "--parse-comments" "-o" (fileName -<.> "tex")

    "dist/thesis.pdf" %> \_ -> do
      files <- getDirectoryFiles (content </> chapter) ["//*.lhs", "//*.lcurry", "//*.v"]
      files2 <- getDirectoryFiles (content </> "figures") ["//*.tex"]
      need (map (\ch -> content </> "figures" </> ch) files2
            ++ map (\ch -> content </> chapter </> ch)
                   ("introduction" <.> "tex" : "conclusion" <.> "tex"
                                     : files))
      b <- doesFileExist "dist/thesis.aux"
      if b then need [dist </> "thesis.bib", dist </> "thesis.tex"] else return ()

      cmd_ "pdflatex" "-shell-escape" "-output-directory" dist (dist </> "thesis.tex")
      cmd_ "pdflatex" "-shell-escape" "-output-directory" dist (dist </> "thesis.tex")
      cmd_ "rm" (dist </> "thesis.bib")
