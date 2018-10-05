import Development.Shake
import Development.Shake.Command
import Development.Shake.FilePath
import Development.Shake.Util

main :: IO ()
main = shakeArgs shakeOptions $ do
    want ["dist/thesis.pdf"]

    phony "clean" $ do
        putNormal "Remove *.aux"
        cmd_ "remove dist/*.aux"

    let content = "content"
        chapter = "chapter"

             
    "dist/thesis.pdf" %> \_ -> do
      files <- getDirectoryFiles (content </> chapter) ["//*.lhs", "//*.lcurry", "//*.v"]
      files2 <- getDirectoryFiles (content </> "figures") ["//*.tex"]
      putNormal (show files)
      need ("thesis.lhs" : map (\ch -> content </> "figures" </> ch) files2
                        ++ map (\ch -> content </> chapter </> ch)
                               ("introduction" <.> "tex" : "conclusion" <.> "tex" : files))
      cmd_ "pdflatex" "-output-directory" "dist" "thesis.tex"

    "thesis.lhs" %> \out -> do
      cmd_ "lhs2tex" out "-o" (out -<.> "tex")

    "content/figures/*.tex" %> \_ -> cmd_ "touch" "thesis.lhs"
    "content/chapter/*.lcurry" %> \_ -> cmd_ "touch" "thesis.lhs"

--    "content/chapter/*.lcurry" %> \out -> do
--      cmd_ "lhs2tex" out "-o" (out -<.> "tex")

    "content/chapter/*.v" %> \out -> do
      let fileName = takeFileName out
      cmd_ "coqdoc" fileName "--latex" "--no-preamble" "--parse-comments" "-o" (fileName -<.> "tex")
