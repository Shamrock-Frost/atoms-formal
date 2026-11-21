import Atoms.Serialize.Document
import Atoms.Molecule.Encoding

open Atoms.Molecule (OGP ShapeData)

namespace Atoms.Serialize

namespace Document

universe u

variable (P : OGP.{u}) [FinEnum P] [DecidableLE P]

def ofOGP (labels : Option (List (List JString)) := none)
    (layout : Option (List (JString × Json)) := none) (extra : List (JString × Json) := []) :
    Document where
  toShapeData := ShapeData.ofOGP P
  labels := labels
  layout := layout
  extra := extra

theorem ofOGP_valid : (ofOGP P).Valid :=
  ⟨ShapeData.ofOGP_valid P, List.nodup_nil, fun _ h => absurd h List.not_mem_nil⟩

theorem ofOGP_toOGP (d : Document) (hd : d.toShapeData.Valid) :
    ofOGP (d.toOGP hd.2) d.labels d.layout d.extra = d := by
  rw [ofOGP, (ShapeData.ofOGP_toOGP_eq_iff hd.2).2 hd.1]

end Document

end Atoms.Serialize
