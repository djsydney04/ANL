import ANL.BootWireIO

def main (args : List String) : IO UInt32 := ANL.Boot.Wire.IOBoundary.run args
