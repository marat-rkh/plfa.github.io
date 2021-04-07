import java.nio.file.Files
import java.nio.file.Path
import kotlin.streams.*

val markdownFiles = Files.list(Path.of("part1")).filter { it.fileName.endsWith(".lagda.md") }.toList()
val arendFiles = Files.list(Path.of("part1-arend/src")).filter { it.fileName.endsWith(".ard") }.toList()

