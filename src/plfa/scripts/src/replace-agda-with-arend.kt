import java.nio.file.Files
import java.nio.file.Path
import kotlin.streams.*

const val agdaMarkdownExt = ".lagda.md"
const val arendExt = ".ard"
const val specialCommentStart = "{-Agda"
const val specialCommentEnd = "Agda-}"

fun main() {
    assert(System.getProperty("user.dir")?.endsWith("plfa/scripts") ?: false)
    replace(Path.of("..", "part1"), Path.of("..", "arend/src/part1"))
}

private fun replace(agdaFilesPath: Path, arendFilesPath: Path) {
    println("INFO: processing $agdaFilesPath and $arendFilesPath")
    val agdaMarkdownFiles = Files.list(agdaFilesPath)
            .filter { it.fileName.toString().endsWith(agdaMarkdownExt) }
            .toList()
    println("INFO: found ${agdaMarkdownFiles.size} Agda Markdown files")
    val arendFiles = Files.list(arendFilesPath)
            .filter { it.fileName.toString().endsWith(arendExt) }
            .toList()
    println("INFO: found ${arendFiles.size} Arend files")
    val allPairs = agdaMarkdownFiles.map { md ->
        val agdaFileName = md.fileName.toString().removeSuffix(agdaMarkdownExt)
        val ard = arendFiles.find { it.fileName.toString().removeSuffix(arendExt) == agdaFileName }
        md to ard
    }
    allPairs.forEach { (agda, arend) -> if (arend == null) println("WARNING: found no Arend file for $agda") }
    val pairs: List<Pair<Path, Path>> = allPairs.filter { it.second != null }.map { it.first to it.second as Path }
    pairs.forEach { (agda, arend) ->
        val arendFileText = Files.readString(arend)
        val parsedEntries = arendFileText
                .splitToSequence(specialCommentStart)
                .filter { it.isNotBlank() }
                .map { part ->
                    val pair = part.split(specialCommentEnd)
                    if (pair.size == 2)
                        pair[0].removePrefix(specialCommentStart).trim() to pair[1].removePrefix(specialCommentEnd).trim()
                    else null
                }
                .toList()
        if (parsedEntries.any { it == null }) {
            println("WARNING: unexpected layout of special comments in $arend")
            return@forEach
        }
        val parsedPairs = parsedEntries.filterNotNull()
        val agdaFileText = Files.readString(agda)
        val updatedFileText = parsedPairs.fold(agdaFileText) { fileText, (key, arendCode) ->
            fileText.replaceFirst("```\n$key\n```", "```\n$arendCode\n```")
        }
        Files.writeString(agda, updatedFileText)
        println("INFO: replaced $agda")
    }
}