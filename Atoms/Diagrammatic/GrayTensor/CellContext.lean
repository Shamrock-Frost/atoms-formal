import Atoms.Diagrammatic.Context.Interchange
import Atoms.Diagrammatic.GrayTensor.ContextTensor

open CategoryTheory Order Atoms.Molecule Atoms.Molecule.OGP Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

section Shape

variable {P Q : OGP.{0}} {U : LowerSet P} {n e : ℕ} {α : Bool}

variable (α) in
private theorem prod_parts (hU : IsMoleculeIn P U) (hdU : krullDim U ≤ n) {C T T' : LowerSet Q}
    (hc : Q.IsPastingAtIn e (xor n.bodd α) C T T') :
    (grayProduct P Q).IsSubmoleculeOf (U ×ˢ C ⊓ U ×ˢ T)
        ((grayProduct P Q).boundary (U ×ˢ C) (e + n) (!α)) ∧
      (grayProduct P Q).IsSubmoleculeOf (U ×ˢ C ⊓ U ×ˢ T)
        ((grayProduct P Q).boundary (U ×ˢ T) (e + n) α) ∧
      (grayProduct P Q).IsSubmoleculeOf ((grayProduct P Q).boundary (U ×ˢ C) (e + n) α)
        ((grayProduct P Q).boundary (U ×ˢ T') (e + n) α) ∧
      (grayProduct P Q).IsSubmoleculeOf ((grayProduct P Q).boundary (U ×ˢ T) (e + n) (!α))
        ((grayProduct P Q).boundary (U ×ˢ T') (e + n) (!α)) := by
  obtain ⟨hg, iA, iB⟩ := hc.isGenPastingIn_cond
  have hp := isGenPastingIn_prod_right hU hdU hg iA iB
  rw [hc.eq_sup, LowerSet.prod_sup]
  refine IsGenPastingIn.cond_parts (α := α) ?_
  generalize n.bodd = c at hp
  cases c <;> cases α <;> exact hp

private theorem prod_inf_sup_boundary (hU : IsMoleculeIn P U) (hdU : krullDim U ≤ n)
    {C T T' : LowerSet Q} (hc : Q.IsPastingAtIn e (xor n.bodd α) C T T')
    (hdT' : krullDim T' ≤ e + 1) :
    U ×ˢ C ⊓ (U ×ˢ T ⊔ (grayProduct P Q).boundary (U ×ˢ T') (e + n) (!α)) =
      (grayProduct P Q).boundary (U ×ˢ C) (e + n) (!α) := by
  have hgU := hU.isGlobular
  have hgC := hc.isMoleculeIn_left.isGlobular
  have hgT' := hc.isMoleculeIn.isGlobular
  refine le_antisymm ?_ fun ⟨a, b⟩ h => ?_
  · rw [inf_sup_left]
    refine sup_le ?_ (inf_boundary_prod_le hgU hgU hgC hgT' (fun _ _ => inf_le_right)
      (fun i β => hc.isSubmoleculeOf_left.inf_boundary_le i β) (e + n) (!α))
    rintro ⟨a, b⟩ ⟨⟨ha, hbC⟩, -, hbT⟩
    refine mem_boundary_prod_of_mem_right hgU hdU hgC ha ?_
    rw [← hc.inf_eq]
    exact ⟨hbC, hbT⟩
  · obtain ⟨i, hi, hai, hbi⟩ := (mem_boundary_prod_of_isGlobular hgU hgC).1 h
    have ha := boundary_le U i _ hai
    refine ⟨⟨ha, boundary_le C _ _ hbi⟩, ?_⟩
    by_cases hin : i < n
    · refine Or.inr ((mem_boundary_prod_of_isGlobular hgU hgT').2 ⟨i, hi, hai, ?_⟩)
      rw [boundary_eq_self (hdT'.trans (by exact_mod_cast (by omega : e + 1 ≤ e + n - i)))]
      exact hc.left_le (boundary_le C _ _ hbi)
    · have hb := hgC.boundary_add_sub_le (α := α) (by omega) hi hbi
      rw [← hc.inf_eq] at hb
      exact Or.inl ⟨ha, hb.2⟩

private theorem isPastingAtIn_prod_sup_boundary (hU : IsMoleculeIn P U) (hdU : krullDim U ≤ n)
    {C T T' : LowerSet Q} (hc : Q.IsPastingAtIn e (xor n.bodd α) C T T')
    (hdT' : krullDim T' ≤ e + 1) :
    (grayProduct P Q).IsPastingAtIn (e + n) α (U ×ˢ C)
      (U ×ˢ T ⊔ (grayProduct P Q).boundary (U ×ˢ T') (e + n) (!α)) (U ×ˢ T') := by
  have hgU := hU.isGlobular
  obtain ⟨g1, g2, g3, g4⟩ := prod_parts α hU hdU hc
  have hT : U ×ˢ C ⊔ U ×ˢ T = U ×ˢ T' := by rw [← LowerSet.prod_sup, hc.eq_sup]
  have hpc := isPastingIn_sup_boundary_cond α g1.le g2.le
  rw [hT] at hpc
  obtain ⟨-, hm1, hm2⟩ := (isPastingIn_cond_iff α).1 hpc
  have hmA := isMoleculeIn_prod hU hc.isMoleculeIn_left
  have hBE : U ×ˢ T ⊓ (grayProduct P Q).boundary (U ×ˢ T') (e + n) (!α) ≤
      (grayProduct P Q).boundary (U ×ˢ T) (e + n) (!α) :=
    inf_boundary_prod_le hgU hgU hc.isMoleculeIn_right.isGlobular hc.isMoleculeIn.isGlobular
      (fun _ _ => inf_le_right) (fun i β => hc.isSubmoleculeOf_right.inf_boundary_le i β) _ _
  refine ⟨hmA, (g4.isSubmoleculeOf_sup (isMoleculeIn_prod hU hc.isMoleculeIn_right)
    (krullDim_boundary_le _ _ _) hBE).isMoleculeIn_right, ?_, prod_inf_sup_boundary hU hdU hc hdT',
    ?_⟩
  · rw [← sup_assoc, hT]
    exact (sup_eq_left.2 (boundary_le _ _ _)).symm
  · rw [prod_inf_sup_boundary hU hdU hc hdT', ← hm2, hm1]
    exact g3.boundary_isSubmoleculeOf_boundary_sup hmA (krullDim_boundary_le _ _ _)
      (inf_boundary_prod_le hgU hgU hc.isMoleculeIn_left.isGlobular hc.isMoleculeIn.isGlobular
        (fun _ _ => inf_le_right) (fun i β => hc.isSubmoleculeOf_left.inf_boundary_le i β) _ α)

private theorem isPastingAtIn_prod_boundary (hU : IsMoleculeIn P U) (hdU : krullDim U ≤ n)
    {T V : LowerSet Q} (hT : IsMoleculeIn Q T) (hV : IsMoleculeIn Q V) (hdV : krullDim V ≤ e + 1)
    (hTV : T ≤ V) (hb : Q.boundary T e (!xor n.bodd α) = Q.boundary V e (!xor n.bodd α))
    (hsub : (grayProduct P Q).IsSubmoleculeOf ((grayProduct P Q).boundary (U ×ˢ T) (e + n) (!α))
      ((grayProduct P Q).boundary (U ×ˢ V) (e + n) (!α))) :
    (grayProduct P Q).IsPastingAtIn (e + n) α (U ×ˢ T)
      ((grayProduct P Q).boundary (U ×ˢ V) (e + n) (!α))
      (U ×ˢ T ⊔ (grayProduct P Q).boundary (U ×ˢ V) (e + n) (!α)) := by
  have hm := prod_inf_boundary_prod_of_le_right hU.isGlobular hdU hT.isGlobular hV.isGlobular hdV
    hTV hb
  refine ⟨isMoleculeIn_prod hU hT, (isMoleculeIn_prod hU hV).boundary _ _, rfl, hm, ?_⟩
  rw [hm, boundary_eq_self (krullDim_boundary_le _ _ _)]
  exact hsub

private theorem isPastingAtIn_prod_stage_right (hU : IsMoleculeIn P U) (hdU : krullDim U ≤ n)
    {C T T' V : LowerSet Q} (hc : Q.IsPastingAtIn e (xor n.bodd α) C T T')
    (hV : IsMoleculeIn Q V) (hdV : krullDim V ≤ e + 1) (hTV : T' ≤ V)
    (hb : Q.boundary T' e (!xor n.bodd α) = Q.boundary V e (!xor n.bodd α))
    (hsub : (grayProduct P Q).IsSubmoleculeOf ((grayProduct P Q).boundary (U ×ˢ T') (e + n) (!α))
      ((grayProduct P Q).boundary (U ×ˢ V) (e + n) (!α))) :
    (grayProduct P Q).IsPastingAtIn (e + n) α (U ×ˢ C)
      ((grayProduct P Q).boundary (U ×ˢ V) (e + n) (!α) ⊔ U ×ˢ T)
      ((grayProduct P Q).boundary (U ×ˢ V) (e + n) (!α) ⊔ U ×ˢ T') := by
  have h₁ := isPastingAtIn_prod_sup_boundary hU hdU hc ((LowerSet.krullDim_mono hTV).trans hdV)
  have h₂ := isPastingAtIn_prod_boundary hU hdU hc.isMoleculeIn hV hdV hTV hb hsub
  have hX := h₁.eq_sup
  rw [hX] at h₂
  obtain ⟨-, h⟩ := IsPastingAtIn.assoc_right { h₁ with eq_sup := rfl } h₂
  rw [sup_assoc, sup_eq_right.2 hsub.le, ← hX] at h
  rwa [sup_comm (U ×ˢ T), sup_comm (U ×ˢ T')] at h

private theorem isSubmoleculeOf_boundary_prod_stage {Y : DiagSet.{u}} (hU : IsMoleculeIn P U)
    (hdU : krullDim U ≤ n) {v : PastingDiagram Y} (Fv : PieceFrame v e (xor n.bodd α)) :
    ∀ j i : ℕ, i + j = Fv.length →
      (grayProduct P v.shape.ogp).IsSubmoleculeOf
        ((grayProduct P v.shape.ogp).boundary (U ×ˢ Fv.stage i) (e + n) (!α))
        ((grayProduct P v.shape.ogp).boundary (U ×ˢ (⊤ : LowerSet v.shape.ogp)) (e + n) (!α))
  | 0, i, h => by
    rw [Nat.add_zero] at h
    subst h
    rw [Fv.stage_length]
    exact IsSubmoleculeOf.refl ((isMoleculeIn_prod hU v.shape.isMolecule).boundary _ _)
  | j + 1, i, h => (prod_parts α hU hdU (Fv.isPastingAtIn i (by omega))).2.2.2.trans
      (isSubmoleculeOf_boundary_prod_stage hU hdU Fv j (i + 1) (by omega))

end Shape

section ShapeLeft

variable {P Q : OGP.{0}} {V : LowerSet Q} {m e : ℕ} {α : Bool}

private theorem prod_parts_left (hV : IsMoleculeIn Q V) (hdV : krullDim V ≤ m)
    {C T T' : LowerSet P} (hc : P.IsPastingAtIn e α C T T') :
    (grayProduct P Q).IsSubmoleculeOf (C ×ˢ V ⊓ T ×ˢ V)
        ((grayProduct P Q).boundary (C ×ˢ V) (e + m) (!α)) ∧
      (grayProduct P Q).IsSubmoleculeOf (C ×ˢ V ⊓ T ×ˢ V)
        ((grayProduct P Q).boundary (T ×ˢ V) (e + m) α) ∧
      (grayProduct P Q).IsSubmoleculeOf ((grayProduct P Q).boundary (C ×ˢ V) (e + m) α)
        ((grayProduct P Q).boundary (T' ×ˢ V) (e + m) α) ∧
      (grayProduct P Q).IsSubmoleculeOf ((grayProduct P Q).boundary (T ×ˢ V) (e + m) (!α))
        ((grayProduct P Q).boundary (T' ×ˢ V) (e + m) (!α)) := by
  obtain ⟨hg, iA, iB⟩ := hc.isGenPastingIn_cond
  have hp := isGenPastingIn_prod_left hV hdV hg iA iB
  rw [hc.eq_sup, LowerSet.sup_prod]
  refine IsGenPastingIn.cond_parts (α := α) ?_
  cases α <;> exact hp

private theorem prod_inf_sup_boundary_left (hV : IsMoleculeIn Q V) (hdV : krullDim V ≤ m)
    {C T T' : LowerSet P} (hc : P.IsPastingAtIn e α C T T') (hdT' : krullDim T' ≤ e + 1) :
    C ×ˢ V ⊓ (T ×ˢ V ⊔ (grayProduct P Q).boundary (T' ×ˢ V) (e + m) (!α)) =
      (grayProduct P Q).boundary (C ×ˢ V) (e + m) (!α) := by
  have hgV := hV.isGlobular
  have hgC := hc.isMoleculeIn_left.isGlobular
  have hgT' := hc.isMoleculeIn.isGlobular
  refine le_antisymm ?_ fun ⟨a, b⟩ h => ?_
  · rw [inf_sup_left]
    refine sup_le ?_ (inf_boundary_prod_le hgC hgT' hgV hgV
      (fun i β => hc.isSubmoleculeOf_left.inf_boundary_le i β) (fun _ _ => inf_le_right) _ _)
    rintro ⟨a, b⟩ ⟨⟨haC, hb⟩, haT, -⟩
    refine mem_boundary_prod_of_mem_left hgC hgV hdV ?_ hb
    rw [← hc.inf_eq]
    exact ⟨haC, haT⟩
  · obtain ⟨i, hi, hai, hbi⟩ := (mem_boundary_prod_of_isGlobular hgC hgV).1 h
    have ha := boundary_le C i _ hai
    have hb := boundary_le V _ _ hbi
    refine ⟨⟨ha, hb⟩, ?_⟩
    by_cases hie : i ≤ e
    · have ha' : a ∈ P.boundary C e (!α) := by
        rcases hie.lt_or_eq with hie | rfl
        · exact hgC.boundary_le_boundary hie _ _ hai
        · exact hai
      rw [← hc.inf_eq] at ha'
      exact Or.inl ⟨ha'.2, hb⟩
    · refine Or.inr ((mem_boundary_prod_of_isGlobular hgT' hgV).2 ⟨i, hi, ?_, hbi⟩)
      rw [boundary_eq_self (hdT'.trans (by exact_mod_cast (by omega : e + 1 ≤ i)))]
      exact hc.left_le ha

private theorem isPastingAtIn_prod_sup_boundary_left (hV : IsMoleculeIn Q V)
    (hdV : krullDim V ≤ m) {C T T' : LowerSet P} (hc : P.IsPastingAtIn e α C T T')
    (hdT' : krullDim T' ≤ e + 1) :
    (grayProduct P Q).IsPastingAtIn (e + m) α (C ×ˢ V)
      (T ×ˢ V ⊔ (grayProduct P Q).boundary (T' ×ˢ V) (e + m) (!α)) (T' ×ˢ V) := by
  have hgV := hV.isGlobular
  obtain ⟨g1, g2, g3, g4⟩ := prod_parts_left hV hdV hc
  have hT : C ×ˢ V ⊔ T ×ˢ V = T' ×ˢ V := by rw [← LowerSet.sup_prod, hc.eq_sup]
  have hpc := isPastingIn_sup_boundary_cond α g1.le g2.le
  rw [hT] at hpc
  obtain ⟨-, hm1, hm2⟩ := (isPastingIn_cond_iff α).1 hpc
  have hmA := isMoleculeIn_prod hc.isMoleculeIn_left hV
  have hBE : T ×ˢ V ⊓ (grayProduct P Q).boundary (T' ×ˢ V) (e + m) (!α) ≤
      (grayProduct P Q).boundary (T ×ˢ V) (e + m) (!α) :=
    inf_boundary_prod_le hc.isMoleculeIn_right.isGlobular hc.isMoleculeIn.isGlobular hgV hgV
      (fun i β => hc.isSubmoleculeOf_right.inf_boundary_le i β) (fun _ _ => inf_le_right) _ _
  refine ⟨hmA, (g4.isSubmoleculeOf_sup (isMoleculeIn_prod hc.isMoleculeIn_right hV)
    (krullDim_boundary_le _ _ _) hBE).isMoleculeIn_right, ?_,
    prod_inf_sup_boundary_left hV hdV hc hdT', ?_⟩
  · rw [← sup_assoc, hT]
    exact (sup_eq_left.2 (boundary_le _ _ _)).symm
  · rw [prod_inf_sup_boundary_left hV hdV hc hdT', ← hm2, hm1]
    exact g3.boundary_isSubmoleculeOf_boundary_sup hmA (krullDim_boundary_le _ _ _)
      (inf_boundary_prod_le hc.isMoleculeIn_left.isGlobular hc.isMoleculeIn.isGlobular hgV hgV
        (fun i β => hc.isSubmoleculeOf_left.inf_boundary_le i β) (fun _ _ => inf_le_right) _ α)

private theorem isPastingAtIn_prod_boundary_left (hV : IsMoleculeIn Q V) (hdV : krullDim V ≤ m)
    {T U : LowerSet P} (hT : IsMoleculeIn P T) (hU : IsMoleculeIn P U) (hdU : krullDim U ≤ e + 1)
    (hTU : T ≤ U) (hb : P.boundary T e (!α) = P.boundary U e (!α))
    (hsub : (grayProduct P Q).IsSubmoleculeOf ((grayProduct P Q).boundary (T ×ˢ V) (e + m) (!α))
      ((grayProduct P Q).boundary (U ×ˢ V) (e + m) (!α))) :
    (grayProduct P Q).IsPastingAtIn (e + m) α (T ×ˢ V)
      ((grayProduct P Q).boundary (U ×ˢ V) (e + m) (!α))
      (T ×ˢ V ⊔ (grayProduct P Q).boundary (U ×ˢ V) (e + m) (!α)) := by
  have hm := prod_inf_boundary_prod_of_le_left hT.isGlobular hU.isGlobular hdU hV.isGlobular hdV
    hTU hb
  refine ⟨isMoleculeIn_prod hT hV, (isMoleculeIn_prod hU hV).boundary _ _, rfl, hm, ?_⟩
  rw [hm, boundary_eq_self (krullDim_boundary_le _ _ _)]
  exact hsub

private theorem isPastingAtIn_prod_stage_left (hV : IsMoleculeIn Q V) (hdV : krullDim V ≤ m)
    {C T T' U : LowerSet P} (hc : P.IsPastingAtIn e α C T T') (hU : IsMoleculeIn P U)
    (hdU : krullDim U ≤ e + 1) (hTU : T' ≤ U) (hb : P.boundary T' e (!α) = P.boundary U e (!α))
    (hsub : (grayProduct P Q).IsSubmoleculeOf ((grayProduct P Q).boundary (T' ×ˢ V) (e + m) (!α))
      ((grayProduct P Q).boundary (U ×ˢ V) (e + m) (!α))) :
    (grayProduct P Q).IsPastingAtIn (e + m) α (C ×ˢ V)
      ((grayProduct P Q).boundary (U ×ˢ V) (e + m) (!α) ⊔ T ×ˢ V)
      ((grayProduct P Q).boundary (U ×ˢ V) (e + m) (!α) ⊔ T' ×ˢ V) := by
  have h₁ := isPastingAtIn_prod_sup_boundary_left hV hdV hc
    ((LowerSet.krullDim_mono hTU).trans hdU)
  have h₂ := isPastingAtIn_prod_boundary_left hV hdV hc.isMoleculeIn hU hdU hTU hb hsub
  have hX := h₁.eq_sup
  rw [hX] at h₂
  obtain ⟨-, h⟩ := IsPastingAtIn.assoc_right { h₁ with eq_sup := rfl } h₂
  rw [sup_assoc, sup_eq_right.2 hsub.le, ← hX] at h
  rwa [sup_comm (T ×ˢ V), sup_comm (T' ×ˢ V)] at h

private theorem isSubmoleculeOf_boundary_prod_stage_left {X : DiagSet.{u}} (hV : IsMoleculeIn Q V)
    (hdV : krullDim V ≤ m) {u : PastingDiagram X} (Fu : PieceFrame u e α) :
    ∀ j i : ℕ, i + j = Fu.length →
      (grayProduct u.shape.ogp Q).IsSubmoleculeOf
        ((grayProduct u.shape.ogp Q).boundary (Fu.stage i ×ˢ V) (e + m) (!α))
        ((grayProduct u.shape.ogp Q).boundary ((⊤ : LowerSet u.shape.ogp) ×ˢ V) (e + m) (!α))
  | 0, i, h => by
    rw [Nat.add_zero] at h
    subst h
    rw [Fu.stage_length]
    exact IsSubmoleculeOf.refl ((isMoleculeIn_prod u.shape.isMolecule hV).boundary _ _)
  | j + 1, i, h => (prod_parts_left hV hdV (Fu.isPastingAtIn i (by omega))).2.2.2.trans
      (isSubmoleculeOf_boundary_prod_stage_left hV hdV Fu j (i + 1) (by omega))

end ShapeLeft

section Frame

variable {X Y : DiagSet.{u}}

private noncomputable def grayFrame (u : RoundPastingDiagram X) {v : PastingDiagram Y} {e : ℕ}
    {α : Bool} (Fv : PieceFrame v e (xor u.dim.bodd α)) (hdv : v.dim ≤ e + 1) :
    PieceFrame (u.toPastingDiagram.grayTensor v) (e + u.dim) α where
  length := Fv.length
  piece i hi := ⟨u.toPastingDiagram.grayTensor (Fv.piece i hi).toPastingDiagram,
    isRound_grayTensor u.isRound (Fv.piece i hi).isRound⟩
  pieceWithin i hi := (Within.refl u.toPastingDiagram).grayTensor (Fv.pieceWithin i hi)
  stage i := OGP.map (u.shape.grayProductIso v.shape).hom
    ((grayProduct _ _).boundary ((⊤ : LowerSet u.shape.ogp) ×ˢ (⊤ : LowerSet v.shape.ogp))
      (e + u.dim) (!α) ⊔ (⊤ : LowerSet u.shape.ogp) ×ˢ Fv.stage i)
  dim_piece i hi := by
    change (u.toPastingDiagram.grayTensor (Fv.piece i hi).toPastingDiagram).dim = _
    rw [dim_grayTensor, Fv.dim_piece i hi]
    omega
  stage_zero := by
    have hdU : krullDim (⊤ : LowerSet u.shape.ogp) ≤ u.dim := by
      rw [LowerSet.krullDim_top, u.shape.krullDim_eq_dimension]; rfl
    rw [Fv.stage_zero, sup_eq_left.2 fun ⟨a, b⟩ ⟨ha, hb⟩ =>
      mem_boundary_prod_of_mem_right u.shape.isMolecule.isGlobular hdU
        v.shape.isMolecule.isGlobular ha hb, map_boundary, LowerSet.top_prod_top, map_top_of_isIso]
  stage_length := by
    rw [Fv.stage_length, LowerSet.top_prod_top, sup_eq_right.2 le_top, map_top_of_isIso]
  isPastingAtIn i hi := by
    have hdU : krullDim (⊤ : LowerSet u.shape.ogp) ≤ u.dim := by
      rw [LowerSet.krullDim_top, u.shape.krullDim_eq_dimension]; rfl
    have hdV : krullDim (⊤ : LowerSet v.shape.ogp) ≤ e + 1 := by
      rw [LowerSet.krullDim_top, v.shape.krullDim_eq_dimension]; exact_mod_cast hdv
    rw [Within.image_grayTensor, Within.image_refl]
    exact (isPastingAtIn_prod_stage_right u.shape.isMolecule hdU (Fv.isPastingAtIn i hi)
      v.shape.isMolecule hdV le_top (Fv.boundary_stage_not (i + 1) hi)
      (isSubmoleculeOf_boundary_prod_stage u.shape.isMolecule hdU Fv _ (i + 1)
        (Nat.add_sub_of_le hi))).map _

private noncomputable def grayFrameLeft {u : PastingDiagram X} {e : ℕ} {α : Bool}
    (Fu : PieceFrame u e α) (v : RoundPastingDiagram Y) (hdu : u.dim ≤ e + 1) :
    PieceFrame (u.grayTensor v.toPastingDiagram) (e + v.dim) α where
  length := Fu.length
  piece i hi := ⟨(Fu.piece i hi).toPastingDiagram.grayTensor v.toPastingDiagram,
    isRound_grayTensor (Fu.piece i hi).isRound v.isRound⟩
  pieceWithin i hi := (Fu.pieceWithin i hi).grayTensor (Within.refl v.toPastingDiagram)
  stage i := OGP.map (u.shape.grayProductIso v.shape).hom
    ((grayProduct _ _).boundary ((⊤ : LowerSet u.shape.ogp) ×ˢ (⊤ : LowerSet v.shape.ogp))
      (e + v.dim) (!α) ⊔ Fu.stage i ×ˢ (⊤ : LowerSet v.shape.ogp))
  dim_piece i hi := by
    change ((Fu.piece i hi).toPastingDiagram.grayTensor v.toPastingDiagram).dim = _
    rw [dim_grayTensor, Fu.dim_piece i hi]
    omega
  stage_zero := by
    have hdV : krullDim (⊤ : LowerSet v.shape.ogp) ≤ v.dim := by
      rw [LowerSet.krullDim_top, v.shape.krullDim_eq_dimension]; rfl
    rw [Fu.stage_zero, sup_eq_left.2 fun ⟨a, b⟩ ⟨ha, hb⟩ =>
      mem_boundary_prod_of_mem_left u.shape.isMolecule.isGlobular v.shape.isMolecule.isGlobular
        hdV ha hb, map_boundary, LowerSet.top_prod_top, map_top_of_isIso]
  stage_length := by
    rw [Fu.stage_length, LowerSet.top_prod_top, sup_eq_right.2 le_top, map_top_of_isIso]
  isPastingAtIn i hi := by
    have hdV : krullDim (⊤ : LowerSet v.shape.ogp) ≤ v.dim := by
      rw [LowerSet.krullDim_top, v.shape.krullDim_eq_dimension]; rfl
    have hdU : krullDim (⊤ : LowerSet u.shape.ogp) ≤ e + 1 := by
      rw [LowerSet.krullDim_top, u.shape.krullDim_eq_dimension]; exact_mod_cast hdu
    rw [Within.image_grayTensor, Within.image_refl]
    exact (isPastingAtIn_prod_stage_left v.shape.isMolecule hdV (Fu.isPastingAtIn i hi)
      u.shape.isMolecule hdU le_top (Fu.boundary_stage_not (i + 1) hi)
      (isSubmoleculeOf_boundary_prod_stage_left v.shape.isMolecule hdV Fu _ (i + 1)
        (Nat.add_sub_of_le hi))).map _

private theorem isPastingAtIn_map_stage {ℓ m : PastingDiagram Y} {k : ℕ} {α : Bool}
    (F : PieceFrame ℓ k α) (w : Within ℓ m) {V : LowerSet m.shape.ogp}
    (hpa : m.shape.ogp.IsPastingAtIn k α w.image V ⊤) {j : ℕ} (hj : j ≤ F.length) :
    OGP.map w.emb (F.stage j) ⊓ V = w.image ⊓ V ∧
      m.shape.ogp.IsPastingAtIn k α (OGP.map w.emb (F.stage j)) V
        (OGP.map w.emb (F.stage j) ⊔ V) := by
  have hB : m.shape.ogp.boundary (OGP.map w.emb (F.stage j)) k (!α) = w.image ⊓ V := by
    rw [← map_boundary, F.boundary_stage_not j hj, ← w.boundary_image, hpa.inf_eq]
  have hm : OGP.map w.emb (F.stage j) ⊓ V = w.image ⊓ V := by
    refine le_antisymm (inf_le_inf_right _ (map_mono w.emb le_top)) (le_inf ?_ inf_le_right)
    calc w.image ⊓ V = OGP.map w.emb (F.stage 0) := by
          rw [hpa.inf_eq, w.boundary_image, F.stage_zero]
      _ ≤ _ := map_mono w.emb (F.stage_zero_le j hj)
  refine ⟨hm, (isMoleculeIn_map_iff _ _).2 (F.isMoleculeIn_stage j hj), hpa.isMoleculeIn_right,
    rfl, hm.trans hB.symm, ?_⟩
  rw [hm]
  exact hpa.isSubmoleculeOf_inf

private noncomputable def PieceFrame.pasteAt {ℓ m : PastingDiagram Y} {k : ℕ} {α : Bool}
    (F : PieceFrame ℓ k α) (w : Within ℓ m) {V : LowerSet m.shape.ogp} {k' : ℕ}
    (hpa : m.shape.ogp.IsPastingAtIn k' α w.image V ⊤) (hk : k' = k) (hV : krullDim V ≤ k) :
    PieceFrame m k α where
  length := F.length
  piece := F.piece
  pieceWithin i hi := (F.pieceWithin i hi).trans w
  stage i := V ⊔ OGP.map w.emb (F.stage i)
  dim_piece := F.dim_piece
  stage_zero := by
    subst hk
    rw [F.stage_zero, ← w.boundary_image, ← hpa.inf_eq, sup_eq_left.2 inf_le_right,
      hpa.boundary_not, boundary_eq_self hV]
  stage_length := by
    rw [F.stage_length, sup_comm]
    exact hpa.eq_sup.symm
  isPastingAtIn i hi := by
    subst hk
    obtain ⟨hm, hst⟩ := isPastingAtIn_map_stage F w hpa hi.le
    rw [Within.image_trans]
    refine ((F.isPastingAtIn i hi).map w.emb).sup_right (sup_comm V _ ▸ hst.isMoleculeIn) ?_
      (sup_comm V _ ▸ hst.isSubmoleculeOf_boundary_left)
    calc OGP.map w.emb (F.pieceWithin i hi).image ⊓ V ≤ w.image ⊓ V :=
          inf_le_inf_right _ (map_mono w.emb le_top)
      _ = OGP.map w.emb (F.stage i) ⊓ V := hm.symm
      _ ≤ _ := inf_le_left

end Frame

namespace CtxExpr.Typed

variable {X Y : DiagSet.{u}} {A : Set (RoundPastingDiagram X)} {B : Set (RoundPastingDiagram Y)}
  {p : Prop}

private theorem exists_side_of_pieceFrame {Z : DiagSet.{u}} {A' : Set (RoundPastingDiagram Z)}
    {H H' : PdHom Z} (α : Bool) {v₀ : PastingDiagram Z} (x : RoundPastingDiagram Z)
    (hdx : x.dim = H.k + 1) {V : PastingDiagram Z} (ι : Within V v₀)
    (hι : v₀.shape.ogp.IsRewritableSubmolecule ι.image ⊤) (h : (x.boundary H.k (!α)).Equiv V)
    (hs : v₀.Equiv (H.side α))
    (e : (H.setSide α ((sidePaste α x.toPastingDiagram H.k ι hι.isSubmoleculeOf h v₀).boundary
      H.k α)).Equiv H')
    {k' : ℕ} (Fx : PieceFrame x.toPastingDiagram k' α) (hk : H.k = k')
    (hA : ∀ i (hi : i < Fx.length), Fx.piece i hi ∈ A') :
    ∃ G : CtxExpr Z, G.Typed A' p H H' ∧ ∀ a, InHom H a → (G.app a).Equiv
      ((CtxExpr.side α x.toPastingDiagram H.k ι hι.isSubmoleculeOf h).app a) := by
  subst hk
  classical
  have hdv₀ := dim_side_of_isRewritable (α := α) _ hdx ι hι h
  have hsv : (v₀.boundary H.k α).Equiv v₀ := equiv_boundary_dim v₀ hdv₀.le α
  have hocc := isSubmoleculeOf_image_sideOcc α H.k ι hι.isSubmoleculeOf hsv
  have happ : sidePaste α x.toPastingDiagram H.k ι hι.isSubmoleculeOf h v₀ =
      pasteAtBoundary x.toPastingDiagram v₀ H.k α (sideOcc α H.k ι hsv) hocc h :=
    sidePaste_of hsv
  set m := pasteAtBoundary x.toPastingDiagram v₀ H.k α (sideOcc α H.k ι hsv) hocc h
  have hpa := Within.isPastingAtIn_pasteAt x.toPastingDiagram v₀ H.k α (sideOcc α H.k ι hsv) hocc h
  have hV : krullDim (Within.pasteAtInr x.toPastingDiagram v₀ H.k α (sideOcc α H.k ι hsv) hocc
      h).image ≤ (H.k : WithBot ℕ∞) := by
    rw [Within.krullDim_image, hdv₀]
  let F := Fx.pasteAt (Within.pasteAtInl _ _ _ _ _ hocc h) hpa rfl hV
  have hs0 : (H.side α).Equiv ((F.stageDiagram 0 (Nat.zero_le _)).boundary H.k α) :=
    hs.symm.trans (Within.equiv_of_image_eq (Within.pasteAtInr _ _ _ _ _ hocc h)
      ((Within.boundary _ _ α).trans (Within.restrictTo m _)) (by
        rw [Within.image_boundary_trans, Within.image_restrictTo, F.stage_zero,
          boundary_eq_self (krullDim_boundary_le _ _ _), hpa.boundary_not, boundary_eq_self hV]))
  have hlen : ((F.stageDiagram F.length le_rfl).boundary H.k α).Equiv (m.boundary H.k α) :=
    Within.equiv_of_image_eq ((Within.boundary _ _ α).trans (Within.restrictTo m _))
      (Within.boundary m _ α) (by
        rw [Within.image_boundary_trans, Within.image_restrictTo, F.stage_length,
          Within.image_boundary])
  rw [happ] at e
  refine ⟨F.ctx F.length, ((F.typed_ctx hA rfl hs0 F.length le_rfl).congr_codomain
    (((PdHom.Equiv.refl H).setSide α hlen).trans e)).mono subset_rfl fun h => h.elim,
    fun a ha => ?_⟩
  have hsa : (a.boundary H.k α).Equiv v₀ := (ha.side α).trans hs.symm
  obtain ⟨hp, -⟩ := sidePaste_equiv_paste_sidePaste (ι := ι) (hι := hι.isSubmoleculeOf) (h := h)
    hdx hdv₀ hsa ha.lt_dim
  rw [happ] at hp
  have e₂ := side_app_equiv_paste (ι := ι) (hι := hι.isSubmoleculeOf) (h := h) hdx hdv₀ hsa
    ha.lt_dim
  rw [show CtxExpr.paste α ((CtxExpr.side α x.toPastingDiagram H.k ι hι.isSubmoleculeOf h).app
    v₀) H.k = CtxExpr.paste α m H.k from congrArg (fun y => CtxExpr.paste α y H.k) happ] at e₂
  exact ((F.ctx_app a hp).trans (paste_app α hp).symm).trans e₂.symm

private theorem exists_of_side_equiv {Z : DiagSet.{u}} {A A' : Set (RoundPastingDiagram Z)}
    (hside : ∀ {H H' : PdHom Z} (α : Bool) {v₀ : PastingDiagram Z} (x : RoundPastingDiagram Z),
      x ∈ A → ∀ (_ : x.dim = H.k + 1) {V : PastingDiagram Z} (ι : Within V v₀)
      (hι : v₀.shape.ogp.IsRewritableSubmolecule ι.image ⊤) (h : (x.boundary H.k (!α)).Equiv V),
      v₀.Equiv (H.side α) → (H.setSide α ((sidePaste α x.toPastingDiagram H.k ι
        hι.isSubmoleculeOf h v₀).boundary H.k α)).Equiv H' →
      ∃ G : CtxExpr Z, G.Typed A' p H H' ∧ ∀ a, InHom H a → (G.app a).Equiv
        ((CtxExpr.side α x.toPastingDiagram H.k ι hι.isSubmoleculeOf h).app a))
    {K K' : PdHom Z} {G : CtxExpr Z} (hG : G.Typed A p K K') :
    ∃ G' : CtxExpr Z, G'.Typed A' p K K' ∧ ∀ a, InHom K a → (G'.app a).Equiv (G.app a) := by
  induction hG with
  | side α x hx hdx ι hι h hs e => exact hside α x hx hdx ι hι h hs e
  | id e => exact ⟨.id, .id e, fun _ _ => .refl _⟩
  | comp ht₁ _ ih₁ ih₂ =>
    obtain ⟨G₁, hG₁, e₁⟩ := ih₁
    obtain ⟨G₂, hG₂, e₂⟩ := ih₂
    exact ⟨.comp G₂ G₁, .comp hG₁ hG₂, fun a ha =>
      (CtxExpr.app_equiv G₂ (e₁ a ha)).trans (e₂ _ (ht₁.mapsInto a ha))⟩
  | @promote k H H₁ H' t hp hk hv hw _ e ih =>
    obtain ⟨G₁, hG₁, e₁⟩ := ih
    exact ⟨G₁, .promote hp hk hv hw hG₁ ((⟨rfl, e₁ _ hv, e₁ _ hw⟩ : PdHom.Equiv
      ⟨H.k, G₁.app H.v, G₁.app H.w⟩ ⟨H.k, t.app H.v, t.app H.w⟩).trans e),
      fun a ha => e₁ a (ha.promote (by omega))⟩

private theorem exists_grayTensor_cells_left_side {H H' : PdHom (grayTensor X Y)} (α : Bool)
    {v₀ : PastingDiagram (grayTensor X Y)} (x : RoundPastingDiagram (grayTensor X Y))
    (hx : x ∈ Set.image2 RoundPastingDiagram.grayTensor A Set.univ) (hdx : x.dim = H.k + 1)
    {V : PastingDiagram (grayTensor X Y)} (ι : Within V v₀)
    (hι : v₀.shape.ogp.IsRewritableSubmolecule ι.image ⊤) (h : (x.boundary H.k (!α)).Equiv V)
    (hs : v₀.Equiv (H.side α))
    (e : (H.setSide α ((sidePaste α x.toPastingDiagram H.k ι hι.isSubmoleculeOf h v₀).boundary
      H.k α)).Equiv H') :
    ∃ G : CtxExpr (grayTensor X Y),
      G.Typed (Set.image2 RoundPastingDiagram.grayTensor A {y | y.shape.ogp.IsAtom}) p H H' ∧
      ∀ a, InHom H a → (G.app a).Equiv
        ((CtxExpr.side α x.toPastingDiagram H.k ι hι.isSubmoleculeOf h).app a) := by
  obtain ⟨u, hu, v, -, rfl⟩ := hx
  have hdx' : u.dim + v.dim = H.k + 1 := (dim_grayTensor _ _).symm.trans hdx
  rcases hv : v.dim with _ | d
  · have hat : v ∈ {y : RoundPastingDiagram Y | y.shape.ogp.IsAtom} :=
      MoleculeShape.isAtom_of_dimension_eq_zero _ hv
    exact ⟨_, .side α (u.grayTensor v) (Set.mem_image2_of_mem hu hat) hdx ι hι h hs e,
      fun _ _ => .refl _⟩
  obtain ⟨L, hL⟩ := PastingDiagram.admitsLayering hv
  exact exists_side_of_pieceFrame α (u.grayTensor v) hdx ι hι h hs e
    (grayFrame u (layerFrame hL (krullDim_top_shape hv) (xor u.dim.bodd α)) hv.le) (by omega)
    fun _ _ => Set.mem_image2_of_mem hu (isAtom_cellOf _ _)

private theorem exists_grayTensor_cells_right_side {H H' : PdHom (grayTensor X Y)} (α : Bool)
    {v₀ : PastingDiagram (grayTensor X Y)} (x : RoundPastingDiagram (grayTensor X Y))
    (hx : x ∈ Set.image2 RoundPastingDiagram.grayTensor Set.univ B) (hdx : x.dim = H.k + 1)
    {V : PastingDiagram (grayTensor X Y)} (ι : Within V v₀)
    (hι : v₀.shape.ogp.IsRewritableSubmolecule ι.image ⊤) (h : (x.boundary H.k (!α)).Equiv V)
    (hs : v₀.Equiv (H.side α))
    (e : (H.setSide α ((sidePaste α x.toPastingDiagram H.k ι hι.isSubmoleculeOf h v₀).boundary
      H.k α)).Equiv H') :
    ∃ G : CtxExpr (grayTensor X Y),
      G.Typed (Set.image2 RoundPastingDiagram.grayTensor {x | x.shape.ogp.IsAtom} B) p H H' ∧
      ∀ a, InHom H a → (G.app a).Equiv
        ((CtxExpr.side α x.toPastingDiagram H.k ι hι.isSubmoleculeOf h).app a) := by
  obtain ⟨u, -, v, hv, rfl⟩ := hx
  have hdx' : u.dim + v.dim = H.k + 1 := (dim_grayTensor _ _).symm.trans hdx
  rcases hu : u.dim with _ | d
  · have hat : u ∈ {x : RoundPastingDiagram X | x.shape.ogp.IsAtom} :=
      MoleculeShape.isAtom_of_dimension_eq_zero _ hu
    exact ⟨_, .side α (u.grayTensor v) (Set.mem_image2_of_mem hat hv) hdx ι hι h hs e,
      fun _ _ => .refl _⟩
  obtain ⟨L, hL⟩ := PastingDiagram.admitsLayering hu
  exact exists_side_of_pieceFrame α (u.grayTensor v) hdx ι hι h hs e
    (grayFrameLeft (layerFrame hL (krullDim_top_shape hu) α) v hu.le) (by omega)
    fun _ _ => Set.mem_image2_of_mem (isAtom_cellOf _ _) hv

theorem exists_grayTensor_cells_left {K K' : PdHom (grayTensor X Y)} {G : CtxExpr (grayTensor X Y)}
    (hG : G.Typed (Set.image2 RoundPastingDiagram.grayTensor A Set.univ) p K K') :
    ∃ G' : CtxExpr (grayTensor X Y),
      G'.Typed (Set.image2 RoundPastingDiagram.grayTensor A {y | y.shape.ogp.IsAtom}) p K K' ∧
      ∀ a, InHom K a → (G'.app a).Equiv (G.app a) :=
  exists_of_side_equiv exists_grayTensor_cells_left_side hG

theorem exists_grayTensor_cells_right {K K' : PdHom (grayTensor X Y)}
    {G : CtxExpr (grayTensor X Y)}
    (hG : G.Typed (Set.image2 RoundPastingDiagram.grayTensor Set.univ B) p K K') :
    ∃ G' : CtxExpr (grayTensor X Y),
      G'.Typed (Set.image2 RoundPastingDiagram.grayTensor {x | x.shape.ogp.IsAtom} B) p K K' ∧
      ∀ a, InHom K a → (G'.app a).Equiv (G.app a) :=
  exists_of_side_equiv exists_grayTensor_cells_right_side hG

end CtxExpr.Typed

end Atoms.Diagrammatic
