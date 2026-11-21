import Atoms.Molecule.Cylinder.PartialMolecule
import Atoms.Molecule.Rewritable.Substitution

universe u

open CategoryTheory Order Set

namespace Atoms.Molecule.OGP

namespace PartialCylinder

section EndStages

variable {U : OGP.{u}} (K : LowerSet U)

def endSet (β : Bool) (m : ℕ) : LowerSet (partialCylinder U K) :=
  copy K β ⊤ ⊔ over K (U.boundary ⊤ m (!β))

def EndStatement (β : Bool) (m : ℕ) : Prop :=
  IsMoleculeIn (partialCylinder U K) (endSet K β m) ∧
    ∀ j (γ : Bool), m < j → (partialCylinder U K).boundary (endSet K β m) j γ =
      copy K β (U.boundary ⊤ j γ) ⊔ over K (U.boundary ⊤ m (!β))

variable {K}

theorem endSet_eq_copy {m : ℕ} {β : Bool} (hsub : U.boundary ⊤ m (!β) ≤ K) :
    endSet K β m = copy K β ⊤ := by
  rw [endSet, over_eq_copy_of_le hsub β]
  exact sup_eq_left.2 (copy_mono β le_top)

variable (hU : IsMolecule U)
include hU

theorem over_boundary_le_succ (m : ℕ) (γ : Bool) :
    over K (U.boundary ⊤ m γ) ≤ over K (U.boundary ⊤ (m + 1) γ) :=
  over_mono (hU.isGlobular.boundary_le_boundary (Nat.lt_succ_self m) γ γ)

theorem boundary_over_boundary_succ (m : ℕ) (α γ : Bool) :
    (partialCylinder U K).boundary (over K (U.boundary ⊤ (m + 1) γ)) (m + 1) α =
      copy K α (U.boundary ⊤ (m + 1) γ) ⊔ over K (U.boundary ⊤ m (!α)) := by
  have hg := hU.isGlobular.boundary (m + 1) γ
  rw [boundary_over_succ hg, boundary_eq_self (krullDim_boundary_le ⊤ (m + 1) γ),
    hU.isGlobular m (m + 1) (Nat.lt_succ_self m)]

theorem endStatement_of_subset {m : ℕ} {β : Bool} (hsub : U.boundary ⊤ m (!β) ≤ K) :
    EndStatement K β m := by
  refine ⟨by rw [endSet_eq_copy hsub]; exact isMoleculeIn_copy hU β, fun j γ hmj => ?_⟩
  rw [endSet_eq_copy hsub, boundary_copy, over_eq_copy_of_le hsub β, ← copy_sup]
  congr 1
  exact (sup_eq_left.2 (hU.isGlobular.boundary_le_boundary hmj (!β) γ)).symm

theorem endSet_succ (β : Bool) (m : ℕ) :
    endSet K β (m + 1) = endSet K β m ⊔ over K (U.boundary ⊤ (m + 1) (!β)) := by
  rw [endSet, endSet, sup_assoc, sup_eq_right.2 (over_boundary_le_succ hU m (!β))]

theorem endSet_inf_over {β : Bool} {m : ℕ} (h : EndStatement K β m) :
    endSet K β m ⊓ over K (U.boundary ⊤ (m + 1) (!β)) =
        (partialCylinder U K).boundary (endSet K β m) (m + 1) (!β) ∧
      endSet K β m ⊓ over K (U.boundary ⊤ (m + 1) (!β)) =
        (partialCylinder U K).boundary (over K (U.boundary ⊤ (m + 1) (!β))) (m + 1) β := by
  have hinter : endSet K β m ⊓ over K (U.boundary ⊤ (m + 1) (!β)) =
      copy K β (U.boundary ⊤ (m + 1) (!β)) ⊔ over K (U.boundary ⊤ m (!β)) := by
    rw [endSet, inf_sup_right, copy_inf_over, top_inf_eq,
      inf_eq_left.2 (over_boundary_le_succ hU m (!β))]
  refine ⟨by rw [hinter, h.2 (m + 1) (!β) (Nat.lt_succ_self m)], ?_⟩
  rw [hinter, boundary_over_boundary_succ hU]

theorem isPastingIn_endSet_succ {β : Bool} {m : ℕ} (h : EndStatement K β m) :
    (partialCylinder U K).IsPastingIn (m + 1)
      (cond β (over K (U.boundary ⊤ (m + 1) (!β))) (endSet K β m))
      (cond β (endSet K β m) (over K (U.boundary ⊤ (m + 1) (!β))))
      (endSet K β (m + 1)) := by
  obtain ⟨h1, h2⟩ := endSet_inf_over hU h
  exact (isPastingIn_cond_iff β).2 ⟨(sup_comm _ _).trans (endSet_succ hU β m).symm,
    (inf_comm _ _).trans h1, (inf_comm _ _).trans h2⟩

theorem endStatement_succ {β : Bool} {m : ℕ} (h : EndStatement K β m) :
    EndStatement K β (m + 1) := by
  have hO := isMoleculeIn_over (K := K) (hU.boundary (m + 1) (!β))
  have hm : IsMoleculeIn (partialCylinder U K) (endSet K β (m + 1)) :=
    (isPastingIn_endSet_succ hU h).isMoleculeIn (Bool.cond_rec_prop β hO h.1)
      (Bool.cond_rec_prop β h.1 hO)
  refine ⟨hm, fun j γ hj => ?_⟩
  have hd : krullDim (over K (U.boundary ⊤ (m + 1) (!β))) ≤ j :=
    (krullDim_over_le (krullDim_boundary_le ⊤ (m + 1) (!β))).trans
      (by exact_mod_cast (show m + 2 ≤ j by omega))
  have hmeet : over K (U.boundary ⊤ (m + 1) (!β)) ⊓ endSet K β m ≤
      (partialCylinder U K).boundary (endSet K β m) j γ := by
    rw [inf_comm, (endSet_inf_over hU h).1, h.2 (m + 1) (!β) (Nat.lt_succ_self m),
      h.2 j γ (by omega)]
    exact sup_le_sup (copy_mono β (hU.isGlobular.boundary_le_boundary (by omega) (!β) γ)) le_rfl
  rw [endSet_succ hU β m, sup_comm, boundary_sup_eq_sup_boundary hd hmeet,
    h.2 j γ (by omega), sup_left_comm,
    sup_eq_left.2 (over_boundary_le_succ (K := K) hU m (!β))]

theorem endStatement_of_le {β : Bool} {k : ℕ} (h : EndStatement K β k) :
    ∀ m, k ≤ m → EndStatement K β m :=
  fun m hm => Nat.le_induction h (fun _ _ ih => endStatement_succ hU ih) m hm

end EndStages

section BottomEnd

variable {U : OGP.{u}} (hU : IsMolecule U) (hr : U.IsRound ⊤) {k : ℕ}
  (hk : (k : WithBot ℕ∞) < krullDim (⊤ : LowerSet U)) {α : Bool} {V : LowerSet U}
  (hV : U.IsSubmoleculeOf V (U.boundary ⊤ k α))
  (hdV : krullDim V = krullDim (U.boundary ⊤ k α))

include hU hr hk hV hdV

theorem over_boundary_eq_copy_sup_over :
    over (hV.hornSetAt hU hr hk hdV) (U.boundary ⊤ k α) =
      copy (hV.hornSetAt hU hr hk hdV) (!α) (U.boundary ⊤ k α) ⊔
        over (hV.hornSetAt hU hr hk hdV) V := by
  classical
  refine le_antisymm (fun z hz => ?_) (sup_le (copy_le_over (!α) _) (over_mono hV.le))
  have hzB := mem_over.1 hz
  by_cases hzK : partialCylinderProj U (hV.hornSetAt hU hr hk hdV) z ∈ hV.hornSetAt hU hr hk hdV
  · exact Or.inl (mem_copy.2 ⟨hzB, (eq_endpoint_of_proj_mem z hzK (!α)).symm⟩)
  · exact Or.inr (mem_over.2 (hV.mem_of_mem_boundary_of_notMem_hornSetAt hU hr hk hdV hzB hzK))

theorem endSet_not_eq :
    endSet (hV.hornSetAt hU hr hk hdV) (!α) k =
      copy (hV.hornSetAt hU hr hk hdV) (!α) ⊤ ⊔ over (hV.hornSetAt hU hr hk hdV) V := by
  rw [endSet, Bool.not_not, over_boundary_eq_copy_sup_over hU hr hk hV hdV,
    ← sup_assoc, sup_eq_left.2 (copy_mono (!α) le_top)]

theorem boundary_over_eq_copy (β : Bool) :
    (partialCylinder U (hV.hornSetAt hU hr hk hdV)).boundary
      (over (hV.hornSetAt hU hr hk hdV) V) k β =
      copy (hV.hornSetAt hU hr hk hdV) β V := by
  have hVm := hV.isMoleculeIn
  have gV := hVm.isGlobular
  have hdk : krullDim V = k := hdV.trans (hU.krullDim_boundary hk.le α)
  rcases k with _ | e
  · rw [boundary_over_zero, boundary_eq_self hdk.le]
  · have hdk' : krullDim V = ((e + 1 : ℕ) : WithBot ℕ∞) := hdk
    have hsub : U.boundary V e (!β) ≤ hV.hornSetAt hU hr hk hdV := by
      rw [← bdry_eq_boundary hdk' (!β)]
      exact (bdry_le_bdryFull V (!β)).trans (hV.bdryFull_le_hornSetAt hU hr hk hdV)
    rw [boundary_over_succ gV, boundary_eq_self hdk.le, over_eq_copy_of_le hsub β]
    exact sup_eq_left.2 (copy_mono β (boundary_le V e (!β)))

theorem isPastingAtIn_endSet_not :
    (partialCylinder U (hV.hornSetAt hU hr hk hdV)).IsPastingAtIn k α
      (over (hV.hornSetAt hU hr hk hdV) V) (copy (hV.hornSetAt hU hr hk hdV) (!α) ⊤)
      (endSet (hV.hornSetAt hU hr hk hdV) (!α) k) := by
  set K := hV.hornSetAt hU hr hk hdV
  have hVm := hV.isMoleculeIn
  have hinter : over K V ⊓ copy K (!α) ⊤ = copy K (!α) V := by
    rw [inf_comm, copy_inf_over, top_inf_eq]
  refine ⟨isMoleculeIn_over (K := K) hVm, isMoleculeIn_copy hU (!α),
    (endSet_not_eq hU hr hk hV hdV).trans (sup_comm _ _),
    by rw [hinter, boundary_over_eq_copy hU hr hk hV hdV], ?_⟩
  rw [hinter, boundary_copy]
  exact isSubmoleculeOf_copy hV (!α)

theorem endStatement_not : EndStatement (hV.hornSetAt hU hr hk hdV) (!α) k := by
  set K := hV.hornSetAt hU hr hk hdV
  have hc := isPastingAtIn_endSet_not hU hr hk hV hdV
  have hdk : krullDim V = k := hdV.trans (hU.krullDim_boundary hk.le α)
  refine ⟨hc.isMoleculeIn, fun j γ hj => ?_⟩
  have hsub : U.boundary ⊤ k α ≤ U.boundary ⊤ j γ :=
    hU.isGlobular.boundary_le_boundary hj α γ
  have hd : krullDim (over K V) ≤ j :=
    (krullDim_over_le hdk.le).trans (by exact_mod_cast (show k + 1 ≤ j by omega))
  have hmeet : over K V ⊓ copy K (!α) ⊤ ≤
      (partialCylinder U K).boundary (copy K (!α) ⊤) j γ := by
    rw [inf_comm, copy_inf_over, top_inf_eq, boundary_copy]
    exact copy_mono _ (hV.le.trans hsub)
  rw [hc.eq_sup, boundary_sup_eq_sup_boundary hd hmeet, boundary_copy, Bool.not_not,
    over_boundary_eq_copy_sup_over hU hr hk hV hdV,
    ← sup_assoc, sup_eq_left.2 (copy_mono _ hsub), sup_comm]

end BottomEnd

section SelfSubstitution

variable {U : OGP.{u}} {V : LowerSet U} (hV : U.IsRewritableSubmolecule V ⊤)

include hV in
theorem isSubstitutionIn_copy :
    (partialCylinder U hV.complement).IsSubstitutionIn
      (copy hV.complement false ⊤) (copy hV.complement false V)
      (copy hV.complement true V) (copy hV.complement true ⊤) := by
  set K := hV.complement
  classical
  let f (α : Bool) := partialCylinderEndpoint U K α
  have hVm := hV.isSubmoleculeOf.isMoleculeIn
  have hbV : U.bdryFull V ≤ K := fun _ hx =>
    ⟨trivial, fun hi => hi.2 (bdryFull_le_properBoundary V hx)⟩
  have hVK : V ⊓ K = U.bdryFull V := by
    rw [← hVm.properBoundary_eq_bdryFull]
    refine SetLike.ext fun x => ?_
    by_cases hx : x ∈ V
    · simp only [LowerSet.mem_inf_iff, hx, true_and]
      exact mem_diff_interior_iff_of_mem (fun _ _ => trivial) hx
    · exact iff_of_false (fun h => hx h.1) (fun h => hx (properBoundary_le V h))
  have hrew : (partialCylinder U K).IsRewritableSubmolecule
      (copy K false V) (copy K false ⊤) := by
    rw [← map_partialCylinderEndpoint, ← map_partialCylinderEndpoint]
    exact (isRewritableSubmolecule_map_iff (f false) V ⊤).2 hV
  refine ⟨hrew, isMoleculeIn_copy hVm true, ?_, ?_, ?_, fun β => ?_, ?_⟩
  · rw [← map_partialCylinderEndpoint]
    exact (isRound_map_iff (f true) V).2 hV.isRound
  · rw [krullDim_copy, krullDim_copy]
  · rw [show (true : Bool) = !false from rfl, copy_inf_copy_not false,
      top_inf_eq, hVK, ← map_partialCylinderEndpoint, ← map_partialCylinderEndpoint,
      map_bdryFull]
  · rw [← map_partialCylinderEndpoint, ← map_partialCylinderEndpoint,
      ← map_bdry, ← map_bdry, map_partialCylinderEndpoint, map_partialCylinderEndpoint]
    have hsub := (bdry_le_bdryFull V β).trans hbV
    exact (over_eq_copy_of_le hsub true).symm.trans (over_eq_copy_of_le hsub false)
  · have hcomp : hrew.complement = copy K false K := by
      have h := congr_arg SetLike.coe (hV.isSubmoleculeOf.map_complement (f false) hV.krullDim_eq
        ((isSubmoleculeOf_map_iff (f false)).2 hV.isSubmoleculeOf)
        (by rw [krullDim_map, krullDim_map]; exact hV.krullDim_eq))
      simp only [f, IsSubmoleculeOf.coe_complement, map_partialCylinderEndpoint] at h
      exact SetLike.coe_injective (by
        rw [IsRewritableSubmolecule.complement, IsSubmoleculeOf.coe_complement]
        exact h.symm)
    have hKK : copy K false K = copy K true K :=
      (over_eq_copy_of_le le_rfl false).symm.trans (over_eq_copy_of_le le_rfl true)
    rw [hcomp, hKK, ← copy_sup]
    congr 1
    refine SetLike.ext fun x => ⟨fun _ => ?_, fun _ => trivial⟩
    by_cases hx : x ∈ U.interior V
    · exact Or.inr hx.1
    · exact Or.inl ⟨trivial, hx⟩

end SelfSubstitution

end PartialCylinder

section HornSetBoundary

open PartialCylinder

variable {U : OGP.{u}} (hU : IsMolecule U) (hr : U.IsRound ⊤) {d : ℕ}
  (hd : krullDim U = d) (hpos : 0 < d) {α : Bool}
  {V : LowerSet U} (hV : U.IsSubmoleculeOf V (U.bdry ⊤ α))
  (hdV : krullDim V = krullDim (U.bdry ⊤ α))

include hU hr hd hpos hV hdV

theorem map_sup_map_eq_boundary {W A M : OGP.{u}} (L : LowerSet W)
    [DecidablePred (· ∈ hV.hornSet hU hr hdV)]
    (f : W ⟶ U) [IsInclusion f] (hfV : map f ⊤ = V)
    (hf : ∀ x, f x ∈ hV.hornSet hU hr hdV ↔ x ∈ L)
    (a : A ≅ partialCylinder W L)
    (enc : partialCylinder U (hV.hornSet hU hr hdV) ≅ M) :
    map (a.hom ≫ embOfEmb (hV.hornSet hU hr hdV) L f hf ≫ enc.hom) ⊤ ⊔
        map (partialCylinderEndpoint U (hV.hornSet hU hr hdV) (!α) ≫ enc.hom) ⊤ =
      M.boundary ⊤ d (!α) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have he : krullDim (⊤ : LowerSet U) = ((e + 1 : ℕ) : WithBot ℕ∞) := by
    rw [LowerSet.krullDim_top, hd]
  have hk : (e : WithBot ℕ∞) < krullDim (⊤ : LowerSet U) := by
    rw [he]; exact_mod_cast Nat.lt_succ_self e
  have hV' : U.IsSubmoleculeOf V (U.boundary ⊤ e α) := bdry_eq_boundary he α ▸ hV
  have hdV' : krullDim V = krullDim (U.boundary ⊤ e α) := bdry_eq_boundary he α ▸ hdV
  have hKeq : hV.hornSet hU hr hdV = hV'.hornSetAt hU hr hk hdV' :=
    hV.hornSet_eq_hornSetAt hU hr hdV he hV' hdV'
  have hcov : over (hV.hornSet hU hr hdV) V ⊔ copy (hV.hornSet hU hr hdV) (!α) ⊤ =
      copy (hV.hornSet hU hr hdV) (!α) ⊤ ⊔
        over (hV.hornSet hU hr hdV) (U.boundary ⊤ e α) := by
    rw [hKeq, sup_comm]
    have h := endSet_not_eq hU hr hk hV' hdV'
    rw [endSet, Bool.not_not] at h
    exact h.symm
  have hb := boundary_partialCylinder_eq (hV.hornSet hU hr hdV) hU hd (!α)
  rw [Bool.not_not] at hb
  have hF : map (embOfEmb (hV.hornSet hU hr hdV) L f hf) ⊤ = over (hV.hornSet hU hr hdV) V := by
    rw [map_embOfEmb_top, hfV]
  rw [map_comp, map_top_of_isIso, map_comp, hF, map_comp, map_partialCylinderEndpoint,
    ← map_sup, hcov, ← hb, map_boundary, map_top_of_isIso]

end HornSetBoundary

end Atoms.Molecule.OGP
