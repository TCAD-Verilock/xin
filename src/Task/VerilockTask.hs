module Task.VerilockTask where

import Synthesis.Generator (GenCase(..), GenerationConfig(..), generateCases)
import Util.Lit (Lit(..))

import Util.FileUtil (createAndWriteFile, copyFileToDirectory)
import System.FilePath ((</>))
import qualified Data.Text as T

baseGenPath :: FilePath
baseGenPath = "./gen/"

statusResourceFilePath :: FilePath
statusResourceFilePath = "./resource/Status.sv"

channelResourceFilePath :: FilePath
channelResourceFilePath = "./resource/Channel.sv"

fileSuffix :: String
fileSuffix = ".sv"

dfSuffix :: String
dfSuffix = "-d"

seed :: Int
seed = 2024

config :: GenerationConfig
config = GenerationConfig {
  _correctCaseNum = 50,
  _defectCaseNum = 50,
  _path = baseGenPath,
  _initialSeed = seed,
  _maxLayer = 30,
  _moduleNumPerLayerRange = (2, 100),
  _constantRange = (0, 10),
  _segmentCount = (2, 8),
  _channelNumPerModuleRange = (1, 500),
  _symmetricStatementRange = (1000, 10000),
  _symmetricLeafModules = (2, 10)
}

caseDirectoryPath :: GenCase -> FilePath
caseDirectoryPath c = basePath c ++ name c

generatedFilePath :: GenCase -> FilePath
generatedFilePath c = caseDirectoryPath c </> (name c ++ fileSuffix)

outputCase :: GenCase -> IO ()
outputCase c = do
  print (states c)
  let p = generatedFilePath c
  let source = lit . ast $ c
  createAndWriteFile p source
  putStrLn ("lines: " ++ (show . length . T.lines $ source))
  let caseDirectory = caseDirectoryPath c
  copyFileToDirectory statusResourceFilePath caseDirectory
  copyFileToDirectory channelResourceFilePath caseDirectory

generateVerilockCases :: IO ()
generateVerilockCases = mapM_ outputCase (generateCases config)