import Atoms.Molecule.Construction.Suspension
import Atoms.Molecule.Gluing.Generated
import Atoms.Molecule.Vertex

universe u

open CategoryTheory Order

namespace Atoms.Molecule.OGP

open SuspCarrier

section Vertex

variable {U V : OGP.{u}}

theorem isMin_of_boundary_zero_eq_Iic (hU : U.IsMolecule) {α : Bool} {v : U}
    (hv : U.boundary ⊤ 0 α = LowerSet.Iic v) : IsMin v := by
  obtain ⟨w, hw, hUw⟩ := exists_boundary_zero_eq_Iic hU α
  have hvw : v ≤ w := LowerSet.mem_Iic_iff.1 (hUw ▸ hv ▸ LowerSet.mem_Iic_iff.2 le_rfl)
  exact (hw.eq_of_le hvw) ▸ hw

variable (φ : PastingIso U V 0)

private theorem isMin_inl {p : U} (hp : IsMin p) : IsMin (glue.inl φ p) := by
  intro x hx
  obtain ⟨p', rfl⟩ := GlueCarrier.exists_inl_eq_of_le_inl hx
  exact GlueCarrier.inl_le_inl (hp (GlueCarrier.inl_le_inl_iff.1 hx))

private theorem isMin_inr {q : V} (hq : IsMin q) : IsMin (glue.inr φ q) := by
  intro x hx
  obtain ⟨q', rfl⟩ := GlueCarrier.exists_inr_eq_of_le_inr hx
  exact GlueCarrier.inr_le_inr (hq (GlueCarrier.inr_le_inr_iff.1 hx))

private theorem orient_eq_of_mem_boundary_zero (hV : V.IsMolecule) {α : Bool} {q e : V}
    (hq : q ∈ V.boundary ⊤ 0 α) (h : q ⋖ e) : V.orient h = α := by
  obtain ⟨b, hb, hVb⟩ := exists_boundary_zero_eq_Iic hV α
  obtain rfl : q = b := hb.eq_of_le (LowerSet.mem_Iic_iff.1 (hVb ▸ hq))
  exact (boundary_zero_eq_Iic_iff hV trivial (grade_eq_zero_iff.2 hb) α).1 hVb e trivial h

theorem boundary_zero_false_glue (hU : U.IsMolecule) (hV : V.IsMolecule) {s : U}
    (hs : U.boundary ⊤ 0 false = LowerSet.Iic s) :
    (glue φ).boundary ⊤ 0 false = LowerSet.Iic (glue.inl φ s) := by
  have hsU : s ∈ U.boundary ⊤ 0 false := hs ▸ LowerSet.mem_Iic_iff.2 le_rfl
  refine (boundary_zero_eq_Iic_iff (isMolecule_glue 0 φ hU hV) trivial
    (grade_eq_zero_iff.2 (isMin_inl φ (isMin_of_boundary_zero_eq_Iic hU hs))) false).2 ?_
  intro e _ h
  rcases glue.exists_inl_or_inr e with ⟨p, rfl⟩ | ⟨q, rfl⟩
  · have h' : s ⋖ p := GlueCarrier.inl_covBy_inl_iff.1 h
    exact (GlueCarrier.orient_inl (φ := φ) h').trans (orient_eq_of_mem_boundary_zero hU hsU h')
  · obtain ⟨q', hq'⟩ := GlueCarrier.exists_inr_eq_of_le_inr h.le
    obtain ⟨hs', rfl⟩ := glue.inl_eq_inr_iff.1 hq'.symm
    revert h
    rw [← hq']
    intro h
    have h' := GlueCarrier.inr_covBy_inr_iff.1 h
    exact (GlueCarrier.orient_inr (φ := φ) h').trans
      (orient_eq_of_mem_boundary_zero hV (φ.hom ⟨s, hs'⟩).2 h')

theorem boundary_zero_true_glue (hU : U.IsMolecule) (hV : V.IsMolecule) {t : V}
    (ht : V.boundary ⊤ 0 true = LowerSet.Iic t) :
    (glue φ).boundary ⊤ 0 true = LowerSet.Iic (glue.inr φ t) := by
  have htV : t ∈ V.boundary ⊤ 0 true := ht ▸ LowerSet.mem_Iic_iff.2 le_rfl
  refine (boundary_zero_eq_Iic_iff (isMolecule_glue 0 φ hU hV) trivial
    (grade_eq_zero_iff.2 (isMin_inr φ (isMin_of_boundary_zero_eq_Iic hV ht))) true).2 ?_
  intro e _ h
  rcases glue.exists_inl_or_inr e with ⟨p, rfl⟩ | ⟨q, rfl⟩
  · obtain ⟨p', hp'⟩ := GlueCarrier.exists_inl_eq_of_le_inl h.le
    obtain ⟨hp, hpt⟩ := glue.inl_eq_inr_iff.1 hp'
    revert h
    rw [← hp']
    intro h
    have h' := GlueCarrier.inl_covBy_inl_iff.1 h
    exact (GlueCarrier.orient_inl (φ := φ) h').trans (orient_eq_of_mem_boundary_zero hU hp h')
  · have h' : t ⋖ q := GlueCarrier.inr_covBy_inr_iff.1 h
    exact (GlueCarrier.orient_inr (φ := φ) h').trans (orient_eq_of_mem_boundary_zero hV htV h')

end Vertex

structure VertexedMolecule : Type (u + 1) where
  ogp : OGP.{u}
  src : ogp
  tgt : ogp
  isMolecule : ogp.IsMolecule
  boundary_false : ogp.boundary ⊤ 0 false = LowerSet.Iic src
  boundary_true : ogp.boundary ⊤ 0 true = LowerSet.Iic tgt

namespace VertexedMolecule

def point : VertexedMolecule.{u} where
  ogp := OGP.point
  src := PUnit.unit
  tgt := PUnit.unit
  isMolecule := isAtom_point.isMoleculeIn
  boundary_false := by
    rw [← boundary_Iic_of_isMin (isMin_point PUnit.unit) 0 false]
    exact congrArg (fun S => OGP.point.boundary S 0 false) LowerSet.Iic_top.symm
  boundary_true := by
    rw [← boundary_Iic_of_isMin (isMin_point PUnit.unit) 0 true]
    exact congrArg (fun S => OGP.point.boundary S 0 true) LowerSet.Iic_top.symm

def susp (A : VertexedMolecule.{u}) : VertexedMolecule.{u} where
  ogp := suspension A.ogp
  src := pole false
  tgt := pole true
  isMolecule := isMolecule_suspension _ A.isMolecule
  boundary_false := by
    rw [← susp_top, boundary_susp_zero ⟨A.src, by simp⟩]
  boundary_true := by
    rw [← susp_top, boundary_susp_zero ⟨A.src, by simp⟩]

def pastingIso (A B : VertexedMolecule.{u}) : PastingIso A.ogp B.ogp 0 :=
  eqToIso (congrArg A.ogp.restrict A.boundary_true) ≪≫
    (isoPointRestrictIic (isMin_of_boundary_zero_eq_Iic A.isMolecule A.boundary_true)).symm ≪≫
    isoPointRestrictIic (isMin_of_boundary_zero_eq_Iic B.isMolecule B.boundary_false) ≪≫
    eqToIso (congrArg B.ogp.restrict B.boundary_false).symm

def wedge (A B : VertexedMolecule.{u}) : VertexedMolecule.{u} where
  ogp := glue (pastingIso A B)
  src := glue.inl _ A.src
  tgt := glue.inr _ B.tgt
  isMolecule := isMolecule_glue 0 _ A.isMolecule B.isMolecule
  boundary_false := boundary_zero_false_glue _ A.isMolecule B.isMolecule A.boundary_false
  boundary_true := boundary_zero_true_glue _ A.isMolecule B.isMolecule B.boundary_true

end VertexedMolecule

inductive PlaneTree : Type
  | node (children : List PlaneTree)

namespace PlaneTree

mutual

def height : PlaneTree → ℕ
  | node ts => heightList ts

def heightList : List PlaneTree → ℕ
  | [] => 0
  | t :: ts => max (height t + 1) (heightList ts)

end

end PlaneTree

inductive IsTheta : OGP.{u} → Prop
  | point : IsTheta point
  | iso {P Q : OGP.{u}} (e : P ≅ Q) (hP : IsTheta P) : IsTheta Q
  | suspend {P : OGP.{u}} (hP : IsTheta P) : IsTheta (suspension P)
  | wedge {P Q : OGP.{u}} (φ : PastingIso P Q 0) (hP : IsTheta P) (hQ : IsTheta Q)
      (hd : (0 : WithBot ℕ∞) < min (krullDim P) (krullDim Q)) : IsTheta (glue φ)

theorem IsTheta.isMolecule {P : OGP.{u}} (h : IsTheta P) : P.IsMolecule := by
  induction h with
  | point => exact isAtom_point.isMoleculeIn
  | iso e _ ih => exact (isMolecule_iff_of_iso e).2 ih
  | suspend _ ih => exact isMolecule_suspension _ ih
  | wedge φ _ _ _ ihP ihQ => exact isMolecule_glue 0 φ ihP ihQ

theorem isTheta_globe (n : ℕ) : IsTheta (globe.{u} n) := by
  induction n with
  | zero => exact .point
  | succ n ih => exact .suspend ih

namespace PlaneTree

mutual

def thetaData : PlaneTree → VertexedMolecule.{u}
  | node ts => thetaDataList ts

def thetaDataList : List PlaneTree → VertexedMolecule.{u}
  | [] => .point
  | [t] => (thetaData t).susp
  | t :: s :: ss => (thetaData t).susp.wedge (thetaDataList (s :: ss))

end

end PlaneTree

def theta (t : PlaneTree) : OGP.{u} :=
  t.thetaData.ogp

@[simp] theorem theta_node_singleton (t : PlaneTree) :
    theta.{u} (.node [t]) = suspension (theta t) :=
  rfl

theorem theta_node_cons_cons (t s : PlaneTree) (ss : List PlaneTree) :
    theta.{u} (.node (t :: s :: ss)) = glue (VertexedMolecule.pastingIso
      (PlaneTree.thetaData t).susp (PlaneTree.thetaData (.node (s :: ss)))) :=
  rfl

private theorem krullDim_glue {U V : OGP.{u}} {k : ℕ} (φ : PastingIso U V k) :
    krullDim (glue φ) = max (krullDim U) (krullDim V) := by
  rw [← LowerSet.krullDim_top, ← glue.map_inl_sup_map_inr φ, LowerSet.krullDim_sup, krullDim_map,
    krullDim_map, LowerSet.krullDim_top, LowerSet.krullDim_top]

private theorem krullDim_suspension {U : OGP.{u}} (x : U) :
    krullDim (suspension U) = krullDim U + 1 := by
  rw [← LowerSet.krullDim_top, ← susp_top, krullDim_susp ⟨x, by simp⟩, LowerSet.krullDim_top]

namespace PlaneTree

mutual

theorem krullDim_thetaData : (t : PlaneTree) → krullDim (thetaData.{u} t).ogp = t.height
  | node ts => krullDim_thetaDataList ts

theorem krullDim_thetaDataList :
    (ts : List PlaneTree) → krullDim (thetaDataList.{u} ts).ogp = heightList ts
  | [] => by
    change krullDim OGP.point.{u} = ((0 : ℕ) : WithBot ℕ∞)
    rw [← LowerSet.krullDim_top, ← LowerSet.Iic_top, LowerSet.krullDim_Iic,
      grade_eq_zero_iff.2 (isMin_point _)]
  | [t] => by
    change krullDim (suspension (thetaData t).ogp) = ((max (height t + 1) 0 : ℕ) : WithBot ℕ∞)
    rw [krullDim_suspension (thetaData t).src, krullDim_thetaData t, Nat.max_zero]
    norm_cast
  | t :: s :: ss => by
    change krullDim (glue (VertexedMolecule.pastingIso (thetaData t).susp
      (thetaDataList (s :: ss)))) = ((max (height t + 1) (heightList (s :: ss)) : ℕ) : WithBot ℕ∞)
    rw [krullDim_glue, krullDim_thetaDataList (s :: ss)]
    change max (krullDim (suspension (thetaData t).ogp)) _ = _
    rw [krullDim_suspension (thetaData t).src, krullDim_thetaData t]
    norm_cast

end

private theorem heightList_cons_pos (t : PlaneTree) (ts : List PlaneTree) :
    0 < heightList (t :: ts) :=
  lt_of_lt_of_le (Nat.succ_pos _) (le_max_left _ _)

mutual

theorem isTheta_thetaData : (t : PlaneTree) → IsTheta (thetaData.{u} t).ogp
  | node ts => isTheta_thetaDataList ts

theorem isTheta_thetaDataList : (ts : List PlaneTree) → IsTheta (thetaDataList.{u} ts).ogp
  | [] => .point
  | [t] => .suspend (isTheta_thetaData t)
  | t :: s :: ss => by
    refine .wedge _ (.suspend (isTheta_thetaData t)) (isTheta_thetaDataList (s :: ss)) ?_
    change (0 : WithBot ℕ∞) <
      min (krullDim (thetaDataList [t]).ogp) (krullDim (thetaDataList (s :: ss)).ogp)
    rw [krullDim_thetaDataList, krullDim_thetaDataList, lt_min_iff]
    exact ⟨by exact_mod_cast heightList_cons_pos t [],
      by exact_mod_cast heightList_cons_pos s ss⟩

end

end PlaneTree

theorem isTheta_theta (t : PlaneTree) : IsTheta (theta.{u} t) :=
  t.isTheta_thetaData

theorem krullDim_theta (t : PlaneTree) : krullDim (theta.{u} t) = t.height :=
  t.krullDim_thetaData

@[instance_reducible]
def VertexedMolecule.decidableMemBoundaryZero (A : VertexedMolecule.{u}) [DecidableLE A.ogp]
    (α : Bool) : DecidablePred (· ∈ A.ogp.boundary ⊤ 0 α) := fun x =>
  match α with
  | false => decidable_of_iff (x ≤ A.src) (A.boundary_false ▸ LowerSet.mem_Iic_iff).symm
  | true => decidable_of_iff (x ≤ A.tgt) (A.boundary_true ▸ LowerSet.mem_Iic_iff).symm

namespace PlaneTree

mutual

def thetaDataInstances : (t : PlaneTree) →
    FinEnum (thetaData.{u} t).ogp × DecidableLE (thetaData.{u} t).ogp
  | node ts => thetaDataListInstances ts

def thetaDataListInstances : (ts : List PlaneTree) →
    FinEnum (thetaDataList.{u} ts).ogp × DecidableLE (thetaDataList.{u} ts).ogp
  | [] => (inferInstanceAs (FinEnum point), inferInstanceAs (DecidableLE point))
  | [t] =>
    letI := (thetaDataInstances t).1
    letI := (thetaDataInstances t).2
    (inferInstanceAs (FinEnum (suspension (thetaData t).ogp)),
      inferInstanceAs (DecidableLE (suspension (thetaData t).ogp)))
  | t :: s :: ss =>
    letI := (thetaDataInstances t).1
    letI := (thetaDataInstances t).2
    letI : FinEnum (thetaData t).susp.ogp :=
      inferInstanceAs (FinEnum (suspension (thetaData t).ogp))
    letI : DecidableLE (thetaData t).susp.ogp :=
      inferInstanceAs (DecidableLE (suspension (thetaData t).ogp))
    letI := (thetaDataListInstances (s :: ss)).1
    letI := (thetaDataListInstances (s :: ss)).2
    letI := (thetaData t).susp.decidableMemBoundaryZero true
    letI := (thetaDataList (s :: ss)).decidableMemBoundaryZero false
    (inferInstanceAs (FinEnum (glue (VertexedMolecule.pastingIso (thetaData t).susp
        (thetaDataList (s :: ss))))),
      inferInstanceAs (DecidableLE (glue (VertexedMolecule.pastingIso (thetaData t).susp
        (thetaDataList (s :: ss))))))

end

end PlaneTree

instance instFinEnumTheta (t : PlaneTree) : FinEnum (theta.{u} t) :=
  t.thetaDataInstances.1

instance instDecidableLETheta (t : PlaneTree) : DecidableLE (theta.{u} t) :=
  t.thetaDataInstances.2

end Atoms.Molecule.OGP
