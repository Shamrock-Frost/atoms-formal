import Atoms.Serialize.Json
import Atoms.Molecule.ShapeData

namespace Atoms.Serialize

structure Document extends Atoms.Molecule.ShapeData where
  labels : Option (List (List JString))
  layout : Option (List (JString × Json))
  extra : List (JString × Json)
  deriving DecidableEq, Inhabited

namespace Document

def formatName : JString := "ogposet".toList

def formatVersion : ℕ := 1

def keyMinus : JString := "-".toList

def keyPlus : JString := "+".toList

def keyFormat : JString := "format".toList

def keyVersion : JString := "version".toList

def keyFaces : JString := "faces".toList

def keyLabels : JString := "labels".toList

def keyLayout : JString := "layout".toList

def knownKeys : List JString := [keyFormat, keyVersion, keyFaces, keyLabels, keyLayout]

def FreshKeys (d : Document) : Prop :=
  (d.extra.map Prod.fst).Nodup ∧ ∀ p ∈ d.extra, p.1 ∉ knownKeys

instance decidableFreshKeys (d : Document) : Decidable d.FreshKeys :=
  inferInstanceAs (Decidable (_ ∧ _))

def Valid (d : Document) : Prop := d.toShapeData.Valid ∧ d.FreshKeys

instance decidableValid (d : Document) : Decidable d.Valid :=
  inferInstanceAs (Decidable (_ ∧ _))

end Document

end Atoms.Serialize
