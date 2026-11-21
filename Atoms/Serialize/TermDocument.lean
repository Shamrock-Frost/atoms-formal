import Atoms.Serialize.RoundTrip
import Atoms.Serialize.Text

open Atoms.Molecule (OGP ShapeData)

namespace Atoms.Serialize

namespace Document

def globe2DualOneDoc : Document where
  faces := [[⟨[], []⟩, ⟨[], []⟩], [⟨[1], [0]⟩, ⟨[1], [0]⟩], [⟨[0], [1]⟩]]
  labels := none
  layout := none
  extra := []

end Document

namespace Term

universe u

def evalOf : (t : Term) → t.Constructible → OGP.{u}
  | .point, _ => OGP.point
  | .globe n, _ => OGP.globe n
  | .simplex n, _ => OGP.simplex n
  | .cube n, _ => OGP.cube n
  | .suspend t, h => OGP.suspension (evalOf t h)
  | .dual t ds, h => OGP.dual (evalOf t h) fun k => decide (k ∈ ds)
  | .gray a b, h => OGP.grayProduct (evalOf a h.1) (evalOf b h.2)
  | .join a b, h => OGP.join (evalOf a h.1) (evalOf b h.2)
  | .paste _ _ _, h => h.elim
  | .atom _ _, h => h.elim

theorem eval_eq_some_evalOf (t : Term) (h : t.Constructible) :
    eval.{u} t = some (evalOf t h) := by
  induction t with
  | point | globe _ | simplex _ | cube _ => rfl
  | suspend t ih | dual t _ ih => simp only [eval, evalOf, ih h, Option.map_some]
  | gray a b iha ihb | join a b iha ihb =>
      simp only [eval, evalOf, iha h.1, ihb h.2, Option.bind_eq_bind, Option.bind_some]
  | paste _ _ _ | atom _ _ => exact h.elim

def evalOfInstances : (t : Term) → (h : t.Constructible) →
    FinEnum (evalOf.{u} t h) × DecidableLE (evalOf.{u} t h)
  | .point, _ => (inferInstanceAs (FinEnum OGP.point), inferInstanceAs (DecidableLE OGP.point))
  | .globe n, _ =>
    (inferInstanceAs (FinEnum (OGP.globe n)), inferInstanceAs (DecidableLE (OGP.globe n)))
  | .simplex n, _ =>
    (inferInstanceAs (FinEnum (OGP.simplex n)), inferInstanceAs (DecidableLE (OGP.simplex n)))
  | .cube n, _ =>
    (inferInstanceAs (FinEnum (OGP.cube n)), inferInstanceAs (DecidableLE (OGP.cube n)))
  | .suspend t, h =>
    letI := (evalOfInstances t h).1
    letI := (evalOfInstances t h).2
    (inferInstanceAs (FinEnum (OGP.suspension (evalOf t h))),
      inferInstanceAs (DecidableLE (OGP.suspension (evalOf t h))))
  | .dual t _, h => evalOfInstances t h
  | .gray a b, h =>
    letI := (evalOfInstances a h.1).1
    letI := (evalOfInstances a h.1).2
    letI := (evalOfInstances b h.2).1
    letI := (evalOfInstances b h.2).2
    (inferInstanceAs (FinEnum (OGP.grayProduct (evalOf a h.1) (evalOf b h.2))),
      inferInstanceAs (DecidableLE (OGP.grayProduct (evalOf a h.1) (evalOf b h.2))))
  | .join a b, h =>
    letI := (evalOfInstances a h.1).1
    letI := (evalOfInstances a h.1).2
    letI := (evalOfInstances b h.2).1
    letI := (evalOfInstances b h.2).2
    (inferInstanceAs (FinEnum (OGP.join (evalOf a h.1) (evalOf b h.2))),
      inferInstanceAs (DecidableLE (OGP.join (evalOf a h.1) (evalOf b h.2))))
  | .paste _ _ _, h => h.elim
  | .atom _ _, h => h.elim

instance instFinEnumEvalOf (t : Term) (h : t.Constructible) : FinEnum (evalOf.{u} t h) :=
  (evalOfInstances t h).1

instance instDecidableLEEvalOf (t : Term) (h : t.Constructible) :
    DecidableLE (evalOf.{u} t h) :=
  (evalOfInstances t h).2

def toDocument (t : Term) : Option Document :=
  if h : t.Constructible then some (Document.ofOGP (evalOf.{0} t h)) else none

theorem isSome_toDocument_iff (t : Term) : (toDocument t).isSome = true ↔ t.Constructible := by
  by_cases h : t.Constructible <;> simp [toDocument, h]

theorem toDocument_of_constructible (t : Term) (h : t.Constructible) :
    toDocument t = some (Document.ofOGP (evalOf.{0} t h)) :=
  dif_pos h

theorem valid_of_toDocument_eq_some {t : Term} {d : Document} (h : toDocument t = some d) :
    d.Valid := by
  have hc : t.Constructible := (isSome_toDocument_iff t).1 (h ▸ rfl)
  rw [toDocument_of_constructible t hc] at h
  exact Option.some.inj h ▸ Document.ofOGP_valid _

def documentOfText (cs : List Char) : Option Document := (parse cs).bind toDocument

theorem documentOfText_print (t : Term) : documentOfText (print t) = toDocument t := by
  rw [documentOfText, parse_print]; rfl

theorem toDocument_point : toDocument .point = some Document.pointDoc := by decide +kernel

theorem toDocument_globe_one : toDocument (.globe 1) = some Document.globe1Doc := by
  decide +kernel

theorem toDocument_simplex_two : toDocument (.simplex 2) = some Document.simplex2Doc := by
  decide +kernel

theorem toDocument_gray_globe_one :
    toDocument (.gray (.globe 1) (.globe 1)) = some Document.squareDoc := by decide +kernel

theorem toDocument_dual_globe_two :
    toDocument (.dual (.globe 2) [1]) = some Document.globe2DualOneDoc := by decide +kernel

example : documentOfText squareText = some Document.squareDoc := by decide +kernel

end Term

end Atoms.Serialize
