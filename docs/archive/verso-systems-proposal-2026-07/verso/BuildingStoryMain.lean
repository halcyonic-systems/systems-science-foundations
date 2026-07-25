import Std.Data.HashMap
import VersoManual
import BuildingStory

open Verso Doc
open Verso.Genre Manual

def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 1
  destination := "_out/building-story"

def main := manualMain (%doc BuildingStory) (config := config)
