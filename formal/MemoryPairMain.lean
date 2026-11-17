import ANL.MemoryWireIO

def main (args : List String) : IO UInt32 := ANL.Memory.Wire.IOBoundary.runPair args
