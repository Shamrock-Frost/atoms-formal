import Atoms.Molecule.Decidable
import Atoms.Molecule.Encoding
import Atoms.Molecule.Gluing.Finite
import Atoms.Molecule.RegularComplex.Basic

open CategoryTheory Order

namespace Atoms.Molecule

open OGP

@[irreducible] def FiniteOGP.ofOGP (P : OGP.{0}) [FinEnum P] [DecidableLE P] : FiniteOGP :=
  ⟨ShapeData.ofOGP P, ShapeData.ofOGP_valid P⟩

unseal FiniteOGP.ofOGP in
@[irreducible] def FiniteOGP.ofOGPIso (P : OGP.{0}) [FinEnum P] [DecidableLE P] :
    P ≅ (FiniteOGP.ofOGP P).ogp :=
  ShapeData.encodingIso P

structure MoleculeShape extends FiniteOGP where
  isMolecule : IsMolecule toFiniteOGP.ogp

namespace MoleculeShape

@[ext] theorem ext {P Q : MoleculeShape} (h : P.toFiniteOGP = Q.toFiniteOGP) : P = Q := by
  cases P; cases Q; cases h; rfl

variable (P : MoleculeShape)

def dimension : ℕ := P.data.faces.length - 1

theorem krullDim_eq_dimension : krullDim P.ogp = P.dimension := by
  obtain ⟨x, -⟩ := P.isMolecule.nonempty
  have hlen : 0 < P.data.faces.length := Nat.zero_lt_of_lt (x : ShapeData.Element P.data).1.2
  have hgrade (y : P.ogp) : grade ℕ y = (y : ShapeData.Element P.data).1.val := rfl
  refine le_antisymm (krullDim_le_coe_iff.2 fun y => ?_) ?_
  · rw [hgrade]
    exact Nat.le_sub_one_of_lt (y : ShapeData.Element P.data).1.2
  · have hrow : P.data.faces[P.dimension]'(by unfold dimension; omega) ≠ [] :=
      (P.valid.2.1.resolve_left (List.ne_nil_of_length_pos hlen)) _ (List.getElem_mem _)
    let t : ShapeData.Element P.data :=
      ⟨⟨P.dimension, by unfold dimension; omega⟩, ⟨0, List.length_pos_of_ne_nil hrow⟩⟩
    exact (grade_le_krullDim (α := P.ogp) t).trans_eq' rfl

theorem krullDim_top_eq {n : ℕ} (hd : P.dimension = n + 1) :
    krullDim (⊤ : LowerSet P.ogp) = n + 1 := by
  rw [LowerSet.krullDim_top, krullDim_eq_dimension, hd]
  push_cast
  rfl

theorem subsingleton_of_dimension_eq_zero (hd : P.dimension = 0) : Subsingleton P.ogp := by
  obtain ⟨x, hx, hxU⟩ := P.isMolecule.exists_eq_Iic_of_krullDim_eq_zero (by
    rw [LowerSet.krullDim_top, P.krullDim_eq_dimension, hd, Nat.cast_zero])
  have hall (y : P.ogp) : y = x := hx.eq_of_le (LowerSet.mem_Iic_iff.1 (hxU ▸ LowerSet.mem_top))
  exact ⟨fun a b => (hall a).trans (hall b).symm⟩

theorem isAtom_of_dimension_eq_zero (h : P.dimension = 0) : P.ogp.IsAtom := by
  have h0 : krullDim (⊤ : LowerSet P.ogp) = 0 := by
    rw [LowerSet.krullDim_top, P.krullDim_eq_dimension, h, Nat.cast_zero]
  obtain ⟨x, -, hx⟩ := P.isMolecule.exists_eq_Iic_of_krullDim_eq_zero h0
  exact ⟨P.isMolecule, x, hx⟩

def IsRound : Prop := P.ogp.IsRound ⊤

theorem isRound_iff : P.IsRound ↔ P.ogp.IsRound ⊤ := Iff.rfl

instance : Decidable P.IsRound := inferInstanceAs (Decidable (P.ogp.IsRound ⊤))

@[implicit_reducible] def rdc : RDCpx.{0} := ⟨⟨P.ogp, isRDC_of_isMolecule P.isMolecule⟩⟩

instance : FinEnum P.rdc.obj.toOGP := inferInstanceAs (FinEnum P.ogp)

instance : DecidableLE P.rdc.obj.toOGP := inferInstanceAs (DecidableLE P.ogp)

@[simp] theorem ofInclusion_id :
    @RDCpx.ofInclusion P.rdc P.rdc (𝟙 P.ogp) (IsInclusion.id P.ogp) = 𝟙 P.rdc := by
  ext x
  rfl

def ofOGP (X : OGP.{0}) [FinEnum X] [DecidableLE X] (h : IsMolecule X) : MoleculeShape :=
  ⟨FiniteOGP.ofOGP X, (isMolecule_iff_of_iso (FiniteOGP.ofOGPIso X)).2 h⟩

theorem dimension_ofOGP (X : OGP.{0}) [FinEnum X] [DecidableLE X] (h : IsMolecule X) :
    ((ofOGP X h).dimension : WithBot ℕ∞) = krullDim X := by
  rw [← krullDim_eq_dimension]
  exact (krullDim_eq_of_orderIso (orderIsoOfIso (FiniteOGP.ofOGPIso X))).symm

theorem isRound_ofOGP (X : OGP.{0}) [FinEnum X] [DecidableLE X] (h : IsMolecule X)
    (hr : X.IsRound ⊤) : (ofOGP X h).IsRound :=
  (isRound_top_iff_of_iso (FiniteOGP.ofOGPIso X)).2 hr

variable {S : LowerSet P.ogp} [DecidablePred (· ∈ S)] (hS : IsMoleculeIn P.ogp S)

def sub : MoleculeShape :=
  ofOGP (P.ogp.restrict S) ((isMolecule_restrict_iff S).2 hS)

def subIso : P.ogp.restrict S ≅ (P.sub hS).ogp :=
  FiniteOGP.ofOGPIso _

def subIncl : (P.sub hS).ogp ⟶ P.ogp :=
  (P.subIso hS).inv ≫ incl S

instance : IsInclusion (P.subIncl hS) :=
  IsInclusion.comp _ _

@[simp] theorem map_subIncl_top : map (P.subIncl hS) ⊤ = S := by
  rw [subIncl, map_comp, map_top_of_isIso, map_incl_top]

theorem dimension_sub : ((P.sub hS).dimension : WithBot ℕ∞) = krullDim S := by
  have h := krullDim_map (P.subIncl hS) ⊤
  rw [map_subIncl_top] at h
  rw [← krullDim_eq_dimension, h, LowerSet.krullDim_top]

theorem isRound_sub_iff : (P.sub hS).IsRound ↔ P.ogp.IsRound S := by
  rw [IsRound, ← isRound_map_iff (P.subIncl hS), map_subIncl_top]

def boundary (k : ℕ) (α : Bool) : MoleculeShape :=
  P.sub (P.isMolecule.boundary k α)

theorem dimension_boundary {k : ℕ} (hk : k ≤ P.dimension) (α : Bool) :
    (P.boundary k α).dimension = k := by
  have h := P.dimension_sub (P.isMolecule.boundary k α)
  rw [P.isMolecule.krullDim_boundary
    (by rw [LowerSet.krullDim_top, krullDim_eq_dimension]; exact_mod_cast hk)] at h
  exact_mod_cast h

theorem dimension_boundary_le (k : ℕ) (α : Bool) : (P.boundary k α).dimension ≤ k := by
  have h := P.dimension_sub (P.isMolecule.boundary k α)
  have hk := krullDim_boundary_le (P := P.ogp) ⊤ k α
  rw [← h] at hk
  exact_mod_cast hk

def boundaryIncl (k : ℕ) (α : Bool) : (P.boundary k α).ogp ⟶ P.ogp :=
  P.subIncl _

instance (k : ℕ) (α : Bool) : IsInclusion (P.boundaryIncl k α) :=
  ⟨IsInclusion.injective (f := P.subIncl (P.isMolecule.boundary k α))⟩

@[simp] theorem map_boundaryIncl_top (k : ℕ) (α : Bool) :
    map (P.boundaryIncl k α) ⊤ = P.ogp.boundary ⊤ k α :=
  P.map_subIncl_top _

def boundaryInclRDC (k : ℕ) (α : Bool) : (P.boundary k α).rdc ⟶ P.rdc :=
  RDCpx.ofInclusion (P.boundaryIncl k α)

theorem isRound_boundary (hP : P.IsRound) (k : ℕ) (α : Bool) : (P.boundary k α).IsRound :=
  (P.isRound_sub_iff _).2 (IsRound.boundary hP k α)

variable (V : MoleculeShape) (k : ℕ)

def gluingIso (ψ : (P.boundary k true).ogp ≅ (V.boundary k false).ogp) :
    P.ogp.restrict (P.ogp.boundary ⊤ k true) ≅ V.ogp.restrict (V.ogp.boundary ⊤ k false) :=
  P.subIso _ ≪≫ ψ ≪≫ (V.subIso _).symm

def paste (ψ : (P.boundary k true).ogp ≅ (V.boundary k false).ogp) : MoleculeShape :=
  ofOGP (glue (P.gluingIso V k ψ)) (isMolecule_glue k _ P.isMolecule V.isMolecule)

def pasteIso (ψ : (P.boundary k true).ogp ≅ (V.boundary k false).ogp) :
    glue (P.gluingIso V k ψ) ≅ (P.paste V k ψ).ogp :=
  FiniteOGP.ofOGPIso _

end MoleculeShape

structure RoundShape extends MoleculeShape where
  isRound : toMoleculeShape.IsRound

@[ext] theorem RoundShape.ext {P Q : RoundShape} (h : P.toMoleculeShape = Q.toMoleculeShape) :
    P = Q := by
  cases P; cases Q; cases h; rfl

end Atoms.Molecule
