import Atoms.Molecule.Gluing.Rewrite
import Atoms.Molecule.Rewritable.Substitution

universe u

open CategoryTheory Order

namespace Atoms.Molecule.OGP

section Substitution

variable {U W : OGP.{u}} {V : LowerSet U} (hV : U.IsRewritableSubmolecule V ⊤)
  (φ : U.restrict (U.bdryFull V) ≅ W.restrict (W.bdryFull ⊤))
include hV

theorem isRewritableSubmolecule_map_inl :
    (glue φ).IsRewritableSubmolecule (map (glue.inl φ) V) (map (glue.inl φ) ⊤) :=
  (isRewritableSubmolecule_map_iff (glue.inl φ) V ⊤).2 hV

def substSupport : LowerSet (glue φ) :=
  (isRewritableSubmolecule_map_inl hV φ).complement ⊔ map (glue.inr φ) ⊤

instance [FinEnum U] [DecidableLE U] [FinEnum W] [DecidableLE W] [DecidablePred (· ∈ V)] :
    DecidablePred (· ∈ substSupport hV φ) :=
  haveI : DecidablePred (· ∈ map (glue.inl φ) ⊤) := decidableMemMap _ _
  haveI : DecidablePred (· ∈ map (glue.inl φ) V) := decidableMemMap _ _
  haveI : DecidablePred (· ∈ map (glue.inr φ) ⊤) := decidableMemMap _ _
  haveI : DecidablePred (· ∈ (glue φ).interior (map (glue.inl φ) V)) := decidableMemInterior _
  haveI : DecidablePred (· ∈ (isRewritableSubmolecule_map_inl hV φ).complement) :=
    IsSubmoleculeOf.decidableMemComplement _ _
  LowerSet.decidableMemSup _ _

variable (hW : IsMolecule W) (hWr : W.IsRound ⊤) (hd : krullDim W = krullDim U) (hφ : φ.IsSigned)

include hW hWr hd hφ in
theorem isSubstitutionIn_glue : (glue φ).IsSubstitutionIn (map (glue.inl φ) ⊤)
    (map (glue.inl φ) V) (map (glue.inr φ) ⊤) (substSupport hV φ) where
  rewritable := isRewritableSubmolecule_map_inl hV φ
  isMoleculeIn_target := (isMoleculeIn_map_iff _ ⊤).2 hW
  isRound_target := (isRound_map_iff _ ⊤).2 hWr
  krullDim_target := by
    rw [krullDim_map, krullDim_map, LowerSet.krullDim_top, hd, hV.krullDim_eq,
      LowerSet.krullDim_top]
  inf_eq := by rw [glue.map_inl_inf_map_inr, map_comp, map_incl_top, map_bdryFull]
  bdry_eq β := by
    rw [← map_bdry, ← map_bdry]
    refine SetLike.ext fun z => ⟨?_, ?_⟩
    · rintro ⟨w, hw, rfl⟩
      have hwF : w ∈ W.bdryFull ⊤ := bdry_le_bdryFull ⊤ β hw
      refine ⟨(φ.inv ⟨w, hwF⟩).1, (hφ β _).2 (by rw [incl_apply, Iso.inv_hom_id_apply]; exact hw),
        glue.inl_eq_inr_iff.2 ⟨(φ.inv ⟨w, hwF⟩).2,
          congrArg Subtype.val (Iso.inv_hom_id_apply φ ⟨w, hwF⟩)⟩⟩
    · rintro ⟨u, hu, rfl⟩
      have huF : u ∈ U.bdryFull V := bdry_le_bdryFull V β hu
      exact ⟨(φ.hom ⟨u, huF⟩).1, (hφ β ⟨u, huF⟩).1 hu,
        (glue.inl_eq_inr_iff.2 ⟨huF, rfl⟩).symm⟩
  eq_sup := rfl

@[implicit_reducible] def substitution : OGP.{u} := (glue φ).restrict (substSupport hV φ)

transfer_instances substitution hV φ with FinEnum DecidableLE

def substInr : W ⟶ substitution hV φ :=
  codRestrict (glue.inr φ) (substSupport hV φ) fun w => Or.inr ⟨w, LowerSet.mem_top, rfl⟩

instance : IsInclusion (substInr hV φ) :=
  ⟨fun _ _ h => IsInclusion.injective (f := glue.inr φ) (congrArg Subtype.val h)⟩

@[reassoc (attr := simp)] theorem substInr_incl :
    substInr hV φ ≫ incl (substSupport hV φ) = glue.inr φ :=
  codRestrict_incl _ _ _

def substInl : U.restrict hV.complement ⟶ substitution hV φ :=
  codRestrict (incl hV.complement ≫ glue.inl φ) (substSupport hV φ) fun x =>
    Or.inl ⟨⟨x.1, LowerSet.mem_top, rfl⟩,
    fun hi => by
      rw [← image_interior] at hi
      obtain ⟨y, hy, hyx⟩ := hi
      have hyx' : y = x.1 := IsInclusion.injective (f := glue.inl φ) hyx
      exact x.2.2 (hyx' ▸ hy)⟩

instance : IsInclusion (substInl hV φ) :=
  ⟨fun _ _ h => IsInclusion.injective (f := incl hV.complement ≫ glue.inl φ)
    (congrArg Subtype.val h)⟩

@[reassoc (attr := simp)] theorem substInl_incl :
    substInl hV φ ≫ incl (substSupport hV φ) = incl hV.complement ≫ glue.inl φ :=
  codRestrict_incl _ _ _

theorem map_substInl_sup_map_substInr : map (substInl hV φ) ⊤ ⊔ map (substInr hV φ) ⊤ = ⊤ := by
  refine map_injective (incl (substSupport hV φ)) ?_
  rw [map_sup, ← map_comp, ← map_comp, substInl_incl, substInr_incl, map_comp, map_incl_top,
    map_incl_top, IsSubmoleculeOf.map_complement (glue.inl φ) hV.isSubmoleculeOf hV.krullDim_eq
      (isRewritableSubmolecule_map_inl hV φ).isSubmoleculeOf
      (isRewritableSubmolecule_map_inl hV φ).krullDim_eq]
  rfl

include hW hWr hd hφ

theorem isMolecule_substitution : IsMolecule (substitution hV φ) :=
  (isMolecule_restrict_iff _).2 (isSubstitutionIn_glue hV φ hW hWr hd hφ).isMoleculeIn

theorem krullDim_substitution : krullDim (substitution hV φ) = krullDim U := by
  have h := (isSubstitutionIn_glue hV φ hW hWr hd hφ).krullDim_eq
  rwa [krullDim_map, LowerSet.krullDim_top] at h

theorem isRewritableSubmolecule_substInr :
    (substitution hV φ).IsRewritableSubmolecule (map (substInr hV φ) ⊤) ⊤ := by
  refine (isRewritableSubmolecule_map_iff (incl (substSupport hV φ)) _ ⊤).1 ?_
  rw [← map_comp, substInr_incl, map_incl_top]
  exact (isSubstitutionIn_glue hV φ hW hWr hd hφ).isRewritableSubmolecule_target

theorem isRound_substitution (hUr : U.IsRound ⊤) : (substitution hV φ).IsRound ⊤ := by
  refine (isRound_map_iff (incl (substSupport hV φ)) ⊤).1 ?_
  rw [map_incl_top]
  exact (isSubstitutionIn_glue hV φ hW hWr hd hφ).isRound ((isRound_map_iff _ ⊤).2 hUr)

end Substitution

section PastingAt

variable {U V : OGP.{u}} {k n : ℕ} {α : Bool} {W : LowerSet V}

@[implicit_reducible] def pastingAt (φ : U.restrict (U.boundary ⊤ k (!α)) ≅ V.restrict W) :
    OGP.{u} :=
  glue φ

variable (φ : U.restrict (U.boundary ⊤ k (!α)) ≅ V.restrict W)

transfer_instances pastingAt φ with DecidableEq DecidableLE FinEnum

theorem map_inl_boundary_pastingAt :
    map (glue.inl φ) (U.boundary ⊤ k (!α)) = map (glue.inl φ) ⊤ ⊓ map (glue.inr φ) ⊤ := by
  rw [glue.map_inl_inf_map_inr, map_comp, map_incl_top]

theorem map_inl_boundary_eq_map_inr_pastingAt :
    map (glue.inl φ) (U.boundary ⊤ k (!α)) = map (glue.inr φ) W := by
  have h := congrArg (fun f : U.restrict (U.boundary ⊤ k (!α)) ⟶ glue φ => map f ⊤)
    (glue.condition φ)
  rw [map_comp, map_comp, map_comp, map_incl_top, map_top_of_isIso, map_incl_top] at h
  exact h

theorem isPastingAtIn_pastingAt (hW : V.IsSubmoleculeOf W (V.boundary ⊤ k α)) (hU : IsMolecule U)
    (hV : IsMolecule V) :
    (pastingAt φ).IsPastingAtIn k α (map (glue.inl φ) ⊤) (map (glue.inr φ) ⊤) ⊤ where
  isMoleculeIn_left := (isMoleculeIn_map_iff _ ⊤).2 hU
  isMoleculeIn_right := (isMoleculeIn_map_iff _ ⊤).2 hV
  eq_sup := (glue.map_inl_sup_map_inr φ).symm
  inf_eq := by rw [← map_inl_boundary_pastingAt, map_boundary]; rfl
  isSubmoleculeOf_inf := by
    rw [← map_inl_boundary_pastingAt, map_inl_boundary_eq_map_inr_pastingAt, ← map_boundary]
    exact (isSubmoleculeOf_map_iff (glue.inr φ)).2 hW

theorem isMolecule_pastingAt (hW : V.IsSubmoleculeOf W (V.boundary ⊤ k α)) (hU : IsMolecule U)
    (hV : IsMolecule V) : IsMolecule (pastingAt φ) :=
  (isPastingAtIn_pastingAt φ hW hU hV).isMoleculeIn

theorem isRound_pastingAt {W : LowerSet V} (hW : V.IsSubmoleculeOf W (V.boundary ⊤ n α))
    (φ : U.restrict (U.boundary ⊤ n (!α)) ≅ V.restrict W) (hU : IsMolecule U) (hV : IsMolecule V)
    (hVr : V.IsRound ⊤) (hn : krullDim V = n + 1) (hd : krullDim U = krullDim V) :
    (pastingAt φ).IsRound ⊤ :=
  (isPastingAtIn_pastingAt φ hW hU hV).isRound ((isRound_map_iff _ ⊤).2 hVr)
    (by rw [krullDim_map, LowerSet.krullDim_top]; exact hn)
    (by
      rw [← glue.map_inl_sup_map_inr φ, LowerSet.krullDim_sup, krullDim_map, krullDim_map,
        LowerSet.krullDim_top, LowerSet.krullDim_top, hd, hn, sup_idem])

end PastingAt

end Atoms.Molecule.OGP
