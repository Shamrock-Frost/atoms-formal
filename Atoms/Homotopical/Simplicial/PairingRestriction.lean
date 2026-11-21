import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.Subcomplex
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic

open CategoryTheory Limits MorphismProperty Simplicial

namespace Atoms.Homotopical

universe u

namespace PairingRestriction

open SSet

variable {X : SSet.{u}} {A B : X.Subcomplex}

def toN (s : (A.preimage B.ι).N) : A.N :=
  Subcomplex.N.mk (B.ι.app _ s.simplex)
    ((nonDegenerate_iff_of_mono B.ι _).2 s.nonDegenerate) s.notMem

theorem toN_le_toN_iff {s t : (A.preimage B.ι).N} : toN s ≤ toN t ↔ s ≤ t := by
  rw [Subcomplex.N.le_iff, Subcomplex.N.le_iff, N.le_iff_exists_mono, N.le_iff_exists_mono]
  refine exists_congr fun f ↦ exists_congr fun _ ↦ ?_
  exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩

theorem toN_injective : Function.Injective (toN (A := A) (B := B)) :=
  fun _ _ h ↦ le_antisymm (toN_le_toN_iff.1 h.le) (toN_le_toN_iff.1 h.ge)

theorem toN_lt_toN_iff {s t : (A.preimage B.ι).N} : toN s < toN t ↔ s < t := by
  simp only [lt_iff_le_not_ge, toN_le_toN_iff]

theorem subcomplex_toN_le (s : (A.preimage B.ι).N) : (toN s).toS.subcomplex ≤ B := by
  rw [Subcomplex.ofSimplex_le_iff]
  exact s.simplex.2

def ofLE (a : A.N) (ha : a.toS.subcomplex ≤ B) : (A.preimage B.ι).N :=
  Subcomplex.N.mk (X := (B : SSet)) ⟨a.simplex, (Subcomplex.ofSimplex_le_iff _ _).1 ha⟩
    ((nonDegenerate_iff_of_mono B.ι
      (⟨a.simplex, (Subcomplex.ofSimplex_le_iff _ _).1 ha⟩ : (B : SSet) _⦋a.dim⦌)).1
        a.nonDegenerate) a.notMem

variable (P : A.Pairing)
  (hP : ∀ x : P.II, x.1.toS.subcomplex ≤ B → (P.p x).1.toS.subcomplex ≤ B)

theorem subcomplex_p_symm_le [P.IsProper] (s : (A.preimage B.ι).N) (hs : toN s ∈ P.I) :
    (P.p.symm ⟨toN s, hs⟩).1.toS.subcomplex ≤ B := by
  refine le_trans ?_ (subcomplex_toN_le s)
  have := P.le (P.p.symm ⟨toN s, hs⟩)
  rw [Equiv.apply_symm_apply] at this
  exact this

include hP in
def pairing [P.IsProper] : (A.preimage B.ι).Pairing where
  I := toN ⁻¹' P.I
  II := toN ⁻¹' P.II
  inter := by rw [← Set.preimage_inter, P.inter, Set.preimage_empty]
  union := by rw [← Set.preimage_union, P.union, Set.preimage_univ]
  p :=
    { toFun s := ⟨ofLE _ (hP _ (subcomplex_toN_le s.1)), (P.p ⟨toN s.1, s.2⟩).2⟩
      invFun s := ⟨ofLE _ (subcomplex_p_symm_le P s.1 s.2), (P.p.symm ⟨toN s.1, s.2⟩).2⟩
      left_inv s := by
        apply Subtype.ext
        apply toN_injective
        exact congrArg Subtype.val (P.p.symm_apply_apply ⟨toN s.1, s.2⟩)
      right_inv s := by
        apply Subtype.ext
        apply toN_injective
        exact congrArg Subtype.val (P.p.apply_symm_apply ⟨toN s.1, s.2⟩) }

theorem toN_pairing_p [P.IsProper] (s : (pairing P hP).II) :
    toN ((pairing P hP).p s).1 = (P.p ⟨toN s.1, s.2⟩).1 := rfl

theorem isUniquelyCodimOneFace_of_map {Y : SSet.{u}} (g : Y ⟶ X) [Mono g] {x y : Y.S}
    (h : (x.map g).IsUniquelyCodimOneFace (y.map g)) : x.IsUniquelyCodimOneFace y := by
  refine ⟨h.1, ?_⟩
  obtain ⟨h₁, h₂⟩ := h
  refine (existsUnique_congr fun f ↦ and_congr_right fun _ ↦ ?_).1 h₂
  change X.map f.op (g.app _ y.simplex) = g.app _ x.simplex ↔ _
  rw [← NatTrans.naturality_apply]
  exact (mono_iff_injective (g.app _)).1 inferInstance |>.eq_iff

instance [P.IsProper] : (pairing P hP).IsProper where
  isUniquelyCodimOneFace s :=
    isUniquelyCodimOneFace_of_map B.ι (P.isUniquelyCodimOneFace ⟨toN s.1, s.2⟩)

instance [P.IsRegular] : (pairing P hP).IsRegular where
  wf := by
    refine Subrelation.wf (r := InvImage P.AncestralRel
      (fun s : (pairing P hP).II ↦ (⟨toN s.1, s.2⟩ : P.II))) ?_ (InvImage.wf _ P.wf)
    intro s t h
    refine ⟨fun hst ↦ h.1 (Subtype.ext (toN_injective (congrArg Subtype.val hst))), ?_⟩
    rw [← toN_pairing_p]
    exact toN_lt_toN_iff.2 h.2

end PairingRestriction

open PairingRestriction in
theorem strongAnodyneExtensions_homOfLE_of_pairing {X : SSet.{u}} {A B : X.Subcomplex}
    (hAB : A ≤ B) (P : A.Pairing) [P.IsRegular]
    (hP : ∀ x : P.II, x.1.toS.subcomplex ≤ B → (P.p x).1.toS.subcomplex ≤ B) :
    SSet.strongAnodyneExtensions (SSet.Subcomplex.homOfLE hAB) := by
  refine ⟨inferInstance, ?_⟩
  rw [SSet.Subcomplex.range_homOfLE hAB]
  exact ⟨pairing P hP, inferInstance⟩

end Atoms.Homotopical
