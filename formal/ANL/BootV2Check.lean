import ANL.BootV2Graph

namespace ANL.Boot.V2

structure WellFormedProgram (p : Program) : Prop where
  metadata : MetadataValid p
  ordered : Ordered false p.functions
  ids : p.functions.map Declaration.id = List.range p.functions.length
  names : (p.functions.map Declaration.name).Nodup
  declarations : ∀ d ∈ p.functions, DeclarationValid p d
  roles : RolesValid p
  discovery : DiscoveryValid p
  acyclic : Acyclic p

def checkProgram (p : Program) : Bool :=
  checkMetadata p && checkOrdered false p.functions &&
  decide (p.functions.map Declaration.id = List.range p.functions.length) &&
  decide (p.functions.map Declaration.name).Nodup &&
  p.functions.all (checkDeclaration p) && checkRoles p && checkDiscovery p && checkGraph p

end ANL.Boot.V2
