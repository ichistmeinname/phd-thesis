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
      files <- getDirectoryFiles (content </> chapter) ["//*.lcurry", "//*.v", "//*.lhs"]
      putNormal (show files)
      need ("thesis.tex" : map (\ch -> content </> chapter </> ch)
                               ("introduction" <.> "tex" : "conclusion" <.> "tex" : files))
      cmd_ "pdflatex" "-output-directory" "dist" "thesis.tex"

    "content/chapter/*.lcurry" %> \out -> do
      cmd_ "lhs2tex" out "-o" (out -<.> "tex")

    "content/chapter/*.v" %> \out -> do
      let fileName = takeFileName out
      cmd_ "coqdoc" fileName "--latex" "--no-preamble" "--parse-comments" "-o" (fileName -<.> "tex")
