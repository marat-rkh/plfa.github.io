# PLFA rewritten in Arend

[arend](arend) directory contains code for the corresponding parts of the book.

[scripts](scripts) directory contains a Kotlin script that replaces Agda code with Arend code in the book's text. 

Arend code consists of snippets separated by special comments. The comments help to find corresponding Agda snippets 
in the Literate Agda files (`*.lagda.md`). The script replaces Agda snippets with the Arend ones in those `*.lagda.md` 
files.