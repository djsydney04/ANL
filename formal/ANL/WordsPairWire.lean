import ANL.WordsWireSafety
import ANL.WordsPair

namespace ANL.Words.Wire

def checkDocuments (coreText mirText : String) : Decode (Program × Mir.Program) := do
  let c ← readCore coreText
  let m ← readMir mirText
  if Pair.check c m then return (c, m)
  else throw (invalid "independent typing or canonical pair check failed")


end ANL.Words.Wire
