import ANL.BootV2WireIO

def main (args : List String) : IO UInt32 := ANL.Boot.V2.Wire.IOBoundary.run args
