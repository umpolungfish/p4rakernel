import Lean

/-! Native retained organism handle. Every IO action continues the same C++
kernel body; snapshots read its actual source, nested frames, frontier,
programs, predictions, observations and action ancestry. -/
namespace Lean.DialetheicOrganism

private opaque BodyImpl : NonemptyType
def Body := BodyImpl.type
instance : Nonempty Body := BodyImpl.property

@[extern "lean_organism_create"]
opaque create (source : @& Sixteen3) : IO Body

@[extern "lean_organism_step"]
opaque step (body : @& Body) : IO Unit

@[extern "lean_organism_attach_vgi"]
opaque attachVGI (body : @& Body) (library : @& String) : IO Unit

@[extern "lean_organism_attach_factor"]
opaque attachFactor (body : @& Body) (source : @& String) (library : @& String) : IO Unit

@[extern "lean_organism_task_closed"]
opaque taskClosed (body : @& Body) : IO Bool

@[extern "lean_organism_snapshot"]
opaque snapshot (body : @& Body) : IO String

end Lean.DialetheicOrganism
