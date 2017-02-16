# Run this file from the vale\tools\Dafny directory 
# This script assumes existence of various files, including:
#   .\DafnyLanguageService.vsix
#   .\DafnyOptions.txt
#   .\z3.exe
# It copies .\DafnyLanguageService.vsix into .\DafnyValeVsPlugin.vsix
# It then adds all the needed files to .\DafnyValeVsPlugin.vsix

"running in $pwd"
$null = [System.Reflection.Assembly]::LoadWithPartialName("System.IO.Compression")
$null = [System.Reflection.Assembly]::LoadWithPartialName("System.IO.Compression.FileSystem")
cp .\DafnyLanguageService.vsix .\DafnyValeVsPlugin.vsix
$zipArchive = [System.IO.Compression.ZipFile]::Open("$pwd\DafnyValeVsPlugin.vsix", [System.IO.Compression.ZipArchiveMode]::Update)

$zipArchive.GetEntry("BoogieAbsInt.dll").Delete()
$null = [System.IO.Compression.ZipFileExtensions]::CreateEntryFromFile($zipArchive, "$pwd\BoogieAbsInt.dll", "BoogieAbsInt.dll")
$zipArchive.GetEntry("BoogieBasetypes.dll").Delete()
$null = [System.IO.Compression.ZipFileExtensions]::CreateEntryFromFile($zipArchive, "$pwd\BoogieBasetypes.dll", "BoogieBasetypes.dll")
$zipArchive.GetEntry("BoogieCodeContractsExtender.dll").Delete()
$null = [System.IO.Compression.ZipFileExtensions]::CreateEntryFromFile($zipArchive, "$pwd\BoogieCodeContractsExtender.dll", "BoogieCodeContractsExtender.dll")
$zipArchive.GetEntry("BoogieConcurrency.dll").Delete()
$null = [System.IO.Compression.ZipFileExtensions]::CreateEntryFromFile($zipArchive, "$pwd\BoogieConcurrency.dll", "BoogieConcurrency.dll")
$zipArchive.GetEntry("BoogieCore.dll").Delete()
$null = [System.IO.Compression.ZipFileExtensions]::CreateEntryFromFile($zipArchive, "$pwd\BoogieCore.dll", "BoogieCore.dll")
$zipArchive.GetEntry("BoogieDoomed.dll").Delete()
$null = [System.IO.Compression.ZipFileExtensions]::CreateEntryFromFile($zipArchive, "$pwd\BoogieDoomed.dll", "BoogieDoomed.dll")
$zipArchive.GetEntry("BoogieExecutionEngine.dll").Delete()
$null = [System.IO.Compression.ZipFileExtensions]::CreateEntryFromFile($zipArchive, "$pwd\BoogieExecutionEngine.dll", "BoogieExecutionEngine.dll")
$zipArchive.GetEntry("BoogieGraph.dll").Delete()
$null = [System.IO.Compression.ZipFileExtensions]::CreateEntryFromFile($zipArchive, "$pwd\BoogieGraph.dll", "BoogieGraph.dll")
$zipArchive.GetEntry("BoogieHoudini.dll").Delete()
$null = [System.IO.Compression.ZipFileExtensions]::CreateEntryFromFile($zipArchive, "$pwd\BoogieHoudini.dll", "BoogieHoudini.dll")
$zipArchive.GetEntry("BoogieModel.dll").Delete()
$null = [System.IO.Compression.ZipFileExtensions]::CreateEntryFromFile($zipArchive, "$pwd\BoogieModel.dll", "BoogieModel.dll")
$zipArchive.GetEntry("BoogieModelViewer.dll").Delete()
$null = [System.IO.Compression.ZipFileExtensions]::CreateEntryFromFile($zipArchive, "$pwd\BoogieModelViewer.dll", "BoogieModelViewer.dll")
$zipArchive.GetEntry("BoogieParserHelper.dll").Delete()
$null = [System.IO.Compression.ZipFileExtensions]::CreateEntryFromFile($zipArchive, "$pwd\BoogieParserHelper.dll", "BoogieParserHelper.dll")
$zipArchive.GetEntry("BoogieVCExpr.dll").Delete()
$null = [System.IO.Compression.ZipFileExtensions]::CreateEntryFromFile($zipArchive, "$pwd\BoogieVCExpr.dll", "BoogieVCExpr.dll")
$zipArchive.GetEntry("BoogieVCGeneration.dll").Delete()
$null = [System.IO.Compression.ZipFileExtensions]::CreateEntryFromFile($zipArchive, "$pwd\BoogieVCGeneration.dll", "BoogieVCGeneration.dll")
$zipArchive.GetEntry("Dafny.exe").Delete()
$null = [System.IO.Compression.ZipFileExtensions]::CreateEntryFromFile($zipArchive, "$pwd\Dafny.exe", "Dafny.exe")
$zipArchive.GetEntry("DafnyLanguageService.dll").Delete()
$null = [System.IO.Compression.ZipFileExtensions]::CreateEntryFromFile($zipArchive, "$pwd\DafnyLanguageService.dll", "DafnyLanguageService.dll")
$zipArchive.GetEntry("DafnyMenu.dll").Delete()
$null = [System.IO.Compression.ZipFileExtensions]::CreateEntryFromFile($zipArchive, "$pwd\DafnyMenu.dll", "DafnyMenu.dll")
$zipArchive.GetEntry("DafnyMenu.pkgdef").Delete()
$null = [System.IO.Compression.ZipFileExtensions]::CreateEntryFromFile($zipArchive, "$pwd\DafnyMenu.pkgdef", "DafnyMenu.pkgdef")
$zipArchive.GetEntry("DafnyOptions.txt").Delete()
$null = [System.IO.Compression.ZipFileExtensions]::CreateEntryFromFile($zipArchive, "$pwd\DafnyOptions.txt", "DafnyOptions.txt")
$zipArchive.GetEntry("DafnyPipeline.dll").Delete()
$null = [System.IO.Compression.ZipFileExtensions]::CreateEntryFromFile($zipArchive, "$pwd\DafnyPipeline.dll", "DafnyPipeline.dll")
$zipArchive.GetEntry("DafnyPrelude.bpl").Delete()
$null = [System.IO.Compression.ZipFileExtensions]::CreateEntryFromFile($zipArchive, "$pwd\DafnyPrelude.bpl", "DafnyPrelude.bpl")
$zipArchive.GetEntry("Newtonsoft.Json.dll").Delete()
$null = [System.IO.Compression.ZipFileExtensions]::CreateEntryFromFile($zipArchive, "$pwd\Newtonsoft.Json.dll", "Newtonsoft.Json.dll")
$zipArchive.GetEntry("Provers.SMTLib.dll").Delete()
$null = [System.IO.Compression.ZipFileExtensions]::CreateEntryFromFile($zipArchive, "$pwd\Provers.SMTLib.dll", "Provers.SMTLib.dll")
$zipArchive.GetEntry("z3.exe").Delete()
$null = [System.IO.Compression.ZipFileExtensions]::CreateEntryFromFile($zipArchive, "$pwd\z3.exe", "z3.exe")
$zipArchive.GetEntry("Z3-LICENSE.txt").Delete()
$null = [System.IO.Compression.ZipFileExtensions]::CreateEntryFromFile($zipArchive, "$pwd\Z3-LICENSE.txt", "Z3-LICENSE.txt")

$zipArchive.Dispose();
"done"
