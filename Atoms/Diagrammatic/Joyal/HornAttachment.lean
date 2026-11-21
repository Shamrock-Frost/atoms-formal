import Atoms.Diagrammatic.Joyal.ConeLifting
import Atoms.Diagrammatic.Marked.Acyclic

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra Opposite MonoidalCategory Simplicial
open Order
open Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape Atoms.Homotopical AugmentedSimplexCategory

universe u

namespace Atoms.Diagrammatic

namespace CoherentContraction

variable {B : Atom} {X : DiagSet.{u}} (C : CoherentContraction B X)

def ext (y : AugmentedSimplexCategory) (x : X.obj (op (cone B (card y)))) :
    X.obj (op (cone B (card (WithInitial.of ⦋0⦌ ⊗ y)))) :=
  C.h.app (op y) x

theorem map_coneHom_inr_ext (y : AugmentedSimplexCategory) (x : X.obj (op (cone B (card y)))) :
    X.map (coneHom B (toOrderHom (inr (WithInitial.of ⦋0⦌) y))).op (C.ext y x) = x :=
  ConcreteCategory.congr_hom (NatTrans.congr_app C.h_comp_counit (op y)) x

theorem map_coneHom_whiskerLeft_ext {y y' : AugmentedSimplexCategory} (θ : y' ⟶ y)
    (x : X.obj (op (cone B (card y)))) :
    X.map (coneHom B (toOrderHom (WithInitial.of ⦋0⦌ ◁ θ))).op (C.ext y x) =
      C.ext y' (X.map (coneHom B (toOrderHom θ)).op x) :=
  (NatTrans.naturality_apply C.h θ.op x).symm

theorem map_coneHom_zeroMul_ext (y : AugmentedSimplexCategory)
    (x : X.obj (op (cone B (card y)))) :
    X.map (coneHom B (toOrderHom
        ((α_ (WithInitial.of ⦋0⦌) (WithInitial.of ⦋0⦌) y).inv ≫ zeroMul ▷ y))).op (C.ext y x) =
      C.ext _ (C.ext y x) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app C.h_comp_comult (op y)) x

theorem ext_mem_coreFiltration (y : AugmentedSimplexCategory) {x : X.obj (op (cone B (card y)))}
    (hx : x ∈ (coreFiltration (B.dimension - 1) X).obj (op (cone B (card y)))) :
    C.ext y x ∈ (coreFiltration (B.dimension - 1) X).obj
      (op (cone B (card (WithInitial.of ⦋0⦌ ⊗ y)))) :=
  C.mem_coreFiltration (op y) x hx

end CoherentContraction

theorem not_isNondegenerate_map_coneHom {X : DiagSet.{u}} (B : Atom)
    {c c' : AugmentedSimplexCategory} (θ : c ⟶ c') (hθ : ¬ Function.Injective (toFun θ))
    (u : X.obj (op (cone B (card c')))) :
    ¬ EZCategory.IsNondegenerate X (X.map (coneHom B (toOrderHom θ)).op u) := by
  obtain ⟨d, π, ε, hπε, hε, him⟩ := exists_comp_eq_injective θ
  have hπ : Function.Surjective (toFun π) := fun j => by
    have : toFun ε j ∈ Finset.univ.image (toFun θ) := by
      rw [← him]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ j)
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 this
    refine ⟨i, hε ?_⟩
    rw [← toFun_comp_apply, hπε, hi]
  have hπi : ¬ Function.Injective (toFun π) := fun h => hθ (by
    rw [← hπε]
    intro i j hij
    rw [toFun_comp_apply, toFun_comp_apply] at hij
    exact h (hε hij))
  obtain ⟨ι, hι⟩ := exists_comp_eq_id_of_surjective π hπ
  have hsplit : IsSplitEpi (coneHom B (toOrderHom π)) :=
    ⟨⟨coneHom B (toOrderHom ι), by
      rw [← coneHom_toOrderHom_comp, hι]
      exact (augmentedCone B).map_id d⟩⟩
  have hcard : card d < card c := by
    have h₁ := Fintype.card_le_of_surjective _ hπ
    have h₂ : card d ≠ card c := fun h => hπi
      ((Fintype.bijective_iff_surjective_and_card _).2 ⟨hπ, by simp [h]⟩).1
    simp only [Fintype.card_fin] at h₁
    omega
  intro hnd
  have hiso := hnd (coneHom B (toOrderHom π)) hsplit
    ⟨X.map (coneHom B (toOrderHom ε)).op u, by
      rw [← Functor.map_comp_apply, ← op_comp, ← coneHom_toOrderHom_comp, hπε]⟩
  have hdim := Atom.dimension_eq_of_iso (asIso (coneHom B (toOrderHom π)))
  rw [dimension_cone, dimension_cone] at hdim
  omega

theorem exists_card_lt_map_coneHom_eq {X : DiagSet.{u}} {B : Atom} (hB0 : 0 < B.dimension)
    {c : AugmentedSimplexCategory}
    {x : X.obj (op (cone B (card c)))}
    (hx : x ∉ (coreFiltration (B.dimension - 1) X).obj (op (cone B (card c))))
    (hnd : ¬ EZCategory.IsNondegenerate X x) :
    ∃ (c' : AugmentedSimplexCategory) (σ : c ⟶ c') (u : X.obj (op (cone B (card c')))),
      card c' < card c ∧ X.map (coneHom B (toOrderHom σ)).op u = x := by
  simp only [EZCategory.IsNondegenerate, not_forall] at hnd
  obtain ⟨V, q, hq, ⟨u₀, hu₀⟩, hnq⟩ := hnd
  obtain ⟨F, s, hF, ⟨e⟩⟩ := exists_isCore_iso_cone V
  have hq' : IsCollapseHom (q ≫ e.hom) := isCollapseHom_of_isSplitEpi _
  have hle := dimension_le_of_isCollapseHom_cone hF (q ≫ e.hom) hq'
  have hx' : X.map (q ≫ e.hom).op (X.map e.inv.op u₀) = x := by
    rw [op_comp, Functor.map_comp_apply, ← Functor.map_comp_apply X e.inv.op e.hom.op, ← op_comp,
      e.hom_inv_id, op_id,
      Functor.map_id_apply, hu₀]
  have hdF : F.dimension = B.dimension := by
    by_contra hne
    exact hx ⟨F, s, q ≫ e.hom, _, by omega, hx'⟩
  have hF0 : 0 < F.dimension := hdF ▸ hB0
  obtain ⟨e', he'⟩ := exists_iso_coneIncl_comp_eq hF hdF.symm (q ≫ e.hom) hq'
  choose τ hτ using exists_conePoint_comp_eq hF hF0 (q ≫ e.hom) hq'
  have hτm := monotone_of_comp_conePoint (q ≫ e.hom) τ hτ
  have hqe : q ≫ e.hom = coneMap e'.hom (card c) ≫ coneHom F ⟨τ, hτm⟩ :=
    cone_hom_ext τ hτ (fun i => by
        rw [conePoint_comp_coneMap_assoc, conePoint_comp_coneHom]
        rfl)
      (by rw [he', coneIncl_comp_coneMap_assoc, coneIncl_comp_coneHom])
  have hsr : s < card c := by
    have h₁ := dimension_le_of_isCollapseHom _ hq'
    rw [dimension_cone, dimension_cone, hdF] at h₁
    rcases Nat.lt_or_eq_of_le (show s ≤ card c by omega) with h | h
    · exact h
    · exfalso
      refine hnq ?_
      have := isIso_of_isCollapseHom_of_dimension_eq _ hq' (by
        rw [dimension_cone, dimension_cone, hdF, h])
      have hqe' : q = (q ≫ e.hom) ≫ e.inv := by simp
      rw [hqe']
      infer_instance
  obtain ⟨c', hc'⟩ := AugmentedSimplexCategory.exists_card_eq s
  subst hc'
  obtain ⟨σ, hσ⟩ := exists_toFun_eq (x := c) (y := c') τ hτm
  refine ⟨c', σ, X.map (coneMap e'.hom (card c')).op (X.map e.inv.op u₀), hsr, ?_⟩
  have hσ' : toOrderHom σ = ⟨τ, hτm⟩ := OrderHom.ext _ _ hσ
  rw [← hx', hqe, hσ', ← Functor.map_comp_apply, ← op_comp, coneHom_comp_coneMap]

theorem isNondegenerate_map_hom {X : DiagSet.{u}} {V V' : Atom} (e : V' ≅ V)
    {w : X.obj (op V)} (hw : EZCategory.IsNondegenerate X w) :
    EZCategory.IsNondegenerate X (X.map e.hom.op w) := by
  intro b q hq ⟨y, hy⟩
  have h : X.map (e.inv ≫ q).op y = w := by
    rw [op_comp, Functor.map_comp_apply, hy, ← Functor.map_comp_apply, ← op_comp,
      e.inv_hom_id, op_id, Functor.map_id_apply]
  have := hw (e.inv ≫ q) inferInstance ⟨y, h⟩
  have h' : q = e.hom ≫ (e.inv ≫ q) := by rw [e.hom_inv_id_assoc]
  rw [h']
  infer_instance

theorem exists_isCore_iso_cone_of_isNondegenerate {X : DiagSet.{u}} {m : ℕ} {V : Atom}
    {w : X.obj (op V)} (hw : w ∈ (coreFiltration m X).obj (op V))
    (hnd : EZCategory.IsNondegenerate X w) :
    ∃ (F : Atom) (s : ℕ), IsCore F ∧ F.dimension ≤ m ∧ Nonempty (V ≅ cone F s) := by
  obtain ⟨B', r, f, z, hB', rfl⟩ := hw
  obtain ⟨V₁, p, i, hp, hi, rfl⟩ := EZCategory.exists_factorization f
  have hpi : IsIso p := hnd p hp ⟨X.map i.op z, by rw [← Functor.map_comp_apply, ← op_comp]⟩
  obtain ⟨F, s, hF, ⟨e⟩⟩ := exists_isCore_iso_cone V
  obtain ⟨F₁, s₁, hF₁, ⟨e₁⟩⟩ := exists_isCore_iso_cone V₁
  have hd₁ := dimension_le_of_isInclusionHom_cone hF₁ (e₁.inv ≫ i) (isInclusionHom_of_mono _)
  obtain ⟨-, ⟨e₂⟩⟩ := eq_and_nonempty_iso_of_iso_cone hF hF₁ (e.symm ≪≫ asIso p ≪≫ e₁)
  exact ⟨F, s, hF, (Atom.dimension_eq_of_iso e₂).trans_le (hd₁.trans hB'), ⟨e⟩⟩

section ConeOne

variable (B : Atom)

noncomputable def coneOneOutputVertex : (cone B 1).ogp :=
  coneIncl B 1 (outputVertexElem B)

def coneOnePoint : (cone B 1).ogp := conePoint B 1 0 default

noncomputable def coneOneEdge : (cone B 1).ogp :=
  coneMap (outputVertex B) 1 (cone atomPoint 1).top

theorem coneCoord_coneOneOutputVertex :
    coneCoord B 1 (coneOneOutputVertex B) = ((outputVertexElem B : WithBot _), ∅) :=
  coneCoord_coneIncl B 1 _

theorem coneCoord_coneOnePoint : coneCoord B 1 (coneOnePoint B) = (⊥, {0}) :=
  coneCoord_conePoint B 1 0 default

theorem coneCoord_coneOneEdge :
    coneCoord B 1 (coneOneEdge B) = ((outputVertexElem B : WithBot _), Finset.univ) := by
  have h := coneCoord_coneMap (outputVertex B) 1 ((cone atomPoint 1).top : WithBot _)
  rw [WithBot.map_coe, coneCoord_top, WithBot.map_coe, outputVertex_apply] at h
  exact h

theorem grade_coneOneOutputVertex : grade ℕ (coneOneOutputVertex B) = 0 := by
  have h := grade_cone_add_one B 1 (coneOneOutputVertex B)
  rw [coneCoord_coneOneOutputVertex, WithBot.grade_coe, dim_outputVertexElem] at h
  simpa using h

theorem grade_coneOnePoint : grade ℕ (coneOnePoint B) = 0 := by
  have h := grade_cone_add_one B 1 (coneOnePoint B)
  rw [coneCoord_coneOnePoint] at h
  simpa using h

theorem grade_coneOneEdge : grade ℕ (coneOneEdge B) = 1 := by
  have h := grade_cone_add_one B 1 (coneOneEdge B)
  rw [coneCoord_coneOneEdge, WithBot.grade_coe, dim_outputVertexElem] at h
  simpa using h

theorem boundary_closure_zero_false_ne_output {b : B.ogp} (hb : grade ℕ b = 1) :
    B.ogp.boundary (.Iic b) 0 false ≠ .Iic (outputVertexElem B) := by
  intro h
  have hmin : IsMin (outputVertexElem B) := grade_eq_zero_iff.1 (dim_outputVertexElem B)
  have hout : B.ogp.boundary ⊤ 0 true = .Iic (outputVertexElem B) :=
    SetLike.coe_injective ((boundary_univ_zero_true_eq_singleton B).trans hmin.Iic_eq.symm)
  have hmem : outputVertexElem B ∈ LowerSet.Iic b :=
    boundary_le _ 0 false (h ▸ LowerSet.mem_Iic_iff.2 le_rfl)
  have hcov : outputVertexElem B ⋖ b :=
    GradeOrder.covBy_of_le_of_grade_eq_add_one (LowerSet.mem_Iic_iff.1 hmem)
      (by rw [dim_outputVertexElem, hb])
  have h₁ := (boundary_zero_eq_Iic_iff (B.isRDC b) hmem (dim_outputVertexElem B) false).1 h b
    (LowerSet.mem_Iic_iff.2 le_rfl) hcov
  have h₂ := (boundary_zero_eq_Iic_iff B.isMolecule LowerSet.mem_top (dim_outputVertexElem B)
    true).1 hout b LowerSet.mem_top hcov
  rw [h₁] at h₂
  exact Bool.false_ne_true h₂

theorem eq_coneOneEdge_of_boundary_eq {y : (cone B 1).ogp} (hy : grade ℕ y = 1)
    (h : (cone B 1).ogp.boundary (.Iic y) 0 false = .Iic (coneOneOutputVertex B)) :
    y = coneOneEdge B := by
  have hd := grade_cone_add_one B 1 y
  rw [hy] at hd
  have hS := Finset.card_le_univ (coneCoord B 1 y).2
  rw [Fintype.card_fin] at hS
  obtain ⟨b, hb⟩ : ∃ b : B.ogp, (coneCoord B 1 y).1 = b := by
    have hne : (coneCoord B 1 y).1 ≠ ⊥ := fun hbot => by
      have h0 : grade ℕ (⊥ : WithBot B.ogp) = 0 := rfl
      rw [hbot, h0] at hd
      omega
    obtain ⟨b, hb⟩ := WithBot.ne_bot_iff_exists.1 hne
    exact ⟨b, hb.symm⟩
  have hmin : IsMin (outputVertexElem B) := grade_eq_zero_iff.1 (dim_outputVertexElem B)
  have hmin' : IsMin (coneOneOutputVertex B) := grade_eq_zero_iff.1 (grade_coneOneOutputVertex B)
  have h' : B.ogp.boundary (.Iic b) 0 false = .Iic (outputVertexElem B) := by
    refine SetLike.coe_injective (Set.image_injective.2 (isInclusionHom_coneIncl B 1) ?_)
    rw [← boundary_closure_zero_false_cone y hb, h, LowerSet.coe_Iic, LowerSet.coe_Iic,
      hmin.Iic_eq, hmin'.Iic_eq, Set.image_singleton]
    rfl
  rw [hb, WithBot.grade_coe] at hd
  rcases Nat.lt_or_ge (grade ℕ b) 1 with hb0 | hb1
  · have hb00 : grade ℕ b = 0 := by omega
    have hb' : b = outputVertexElem B := by
      have hmem : b ∈ B.ogp.boundary (.Iic b) 0 false := by
        rw [boundary_Iic_of_isMin (grade_eq_zero_iff.1 hb00) 0 false]
        exact LowerSet.mem_Iic_iff.2 le_rfl
      rw [h'] at hmem
      exact hmin.eq_of_le (LowerSet.mem_Iic_iff.1 hmem)
    refine eq_of_coneCoord_eq ?_
    rw [coneCoord_coneOneEdge, ← hb', ← hb]
    refine Prod.ext rfl (Finset.eq_univ_of_card _ ?_)
    rw [Fintype.card_fin]
    omega
  · exact absurd h' (boundary_closure_zero_false_ne_output B (by omega))

theorem boundary_closure_zero_false_ne_coneOnePoint {y : (cone B 1).ogp}
    (hy : grade ℕ y = 1) :
    (cone B 1).ogp.boundary (.Iic y) 0 false ≠ .Iic (coneOnePoint B) := by
  intro h
  have hd := grade_cone_add_one B 1 y
  rw [hy] at hd
  have hS := Finset.card_le_univ (coneCoord B 1 y).2
  rw [Fintype.card_fin] at hS
  obtain ⟨b, hb⟩ : ∃ b : B.ogp, (coneCoord B 1 y).1 = b := by
    have hne : (coneCoord B 1 y).1 ≠ ⊥ := fun hbot => by
      have h0 : grade ℕ (⊥ : WithBot B.ogp) = 0 := rfl
      rw [hbot, h0] at hd
      omega
    obtain ⟨b, hb⟩ := WithBot.ne_bot_iff_exists.1 hne
    exact ⟨b, hb.symm⟩
  have hmem : coneOnePoint B ∈ coneIncl B 1 '' (B.ogp.boundary (.Iic b) 0 false : Set B.ogp) := by
    rw [← boundary_closure_zero_false_cone y hb, h]
    exact LowerSet.mem_Iic_iff.2 le_rfl
  obtain ⟨z, -, hz⟩ := hmem
  have := congrArg (coneCoord B 1 ∘ WithBot.some) hz
  simp only [Function.comp_apply, coneCoord_coneIncl, coneCoord_coneOnePoint] at this
  exact WithBot.coe_ne_bot (congrArg Prod.fst this)

theorem closure_coneOneEdge_subset :
    (LowerSet.Iic (coneOneEdge B) : Set (cone B 1).ogp) ⊆
      {coneOneOutputVertex B, coneOnePoint B, coneOneEdge B} := by
  intro z hz
  rw [SetLike.mem_coe, LowerSet.mem_Iic_iff, le_iff_coneCoord, coneCoord_coneOneEdge] at hz
  obtain ⟨hzb, -⟩ := hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have hS : (coneCoord B 1 z).2 = ∅ ∨ (coneCoord B 1 z).2 = Finset.univ := by
    rcases Finset.eq_empty_or_nonempty (coneCoord B 1 z).2 with h | ⟨i, hi⟩
    · exact Or.inl h
    · refine Or.inr (Finset.eq_univ_of_forall fun j => ?_)
      rwa [Subsingleton.elim j i]
  induction hb : (coneCoord B 1 z).1 using WithBot.recBotCoe with
  | bot =>
    rcases hS with hS | hS
    · exact absurd (coneCoord_eq_bot_iff.1 (Prod.ext hb hS)) WithBot.coe_ne_bot
    · refine Or.inr (Or.inl (eq_of_coneCoord_eq ?_))
      rw [coneCoord_coneOnePoint]
      exact Prod.ext hb (hS.trans (Finset.eq_singleton_iff_unique_mem.2
        ⟨Finset.mem_univ _, fun x _ => Subsingleton.elim _ _⟩))
  | coe b =>
    rw [hb] at hzb
    have hbt : b = outputVertexElem B := GradeOrder.eq_of_le_of_grade_le
      (WithBot.coe_le_coe.1 hzb) (by rw [dim_outputVertexElem]; exact Nat.zero_le _)
    rcases hS with hS | hS
    · refine Or.inl (eq_of_coneCoord_eq ?_)
      rw [coneCoord_coneOneOutputVertex]
      exact Prod.ext (hb.trans (by rw [hbt])) hS
    · refine Or.inr (Or.inr (eq_of_coneCoord_eq ?_))
      rw [coneCoord_coneOneEdge]
      exact Prod.ext (hb.trans (by rw [hbt])) hS

theorem subset_of_isMoleculeIn_cone_one {W : LowerSet (cone B 1).ogp}
    (hW : IsMoleculeIn (cone B 1).ogp W) (hd : krullDim W ≤ 1) :
    ((cone B 1).ogp.boundary W 0 false = .Iic (coneOneOutputVertex B) →
        (W : Set (cone B 1).ogp) ⊆ {coneOneOutputVertex B, coneOnePoint B, coneOneEdge B}) ∧
      ((cone B 1).ogp.boundary W 0 false = .Iic (coneOnePoint B) →
        (W : Set (cone B 1).ogp) ⊆ {coneOnePoint B}) := by
  have hpoint : ∀ x : (cone B 1).ogp, IsMin x →
      ((cone B 1).ogp.boundary (.Iic x) 0 false = .Iic (coneOneOutputVertex B) →
        ((LowerSet.Iic x : LowerSet (cone B 1).ogp) : Set (cone B 1).ogp) ⊆
          {coneOneOutputVertex B, coneOnePoint B, coneOneEdge B}) ∧
      ((cone B 1).ogp.boundary (.Iic x) 0 false = .Iic (coneOnePoint B) →
        ((LowerSet.Iic x : LowerSet (cone B 1).ogp) : Set (cone B 1).ogp) ⊆
          {coneOnePoint B}) := by
    intro x hx
    rw [boundary_Iic_of_isMin hx 0 false]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [h, LowerSet.coe_Iic, (grade_eq_zero_iff.1 (grade_coneOneOutputVertex B)).Iic_eq]
      exact Set.singleton_subset_iff.2 (Set.mem_insert _ _)
    · rw [h, LowerSet.coe_Iic, (grade_eq_zero_iff.1 (grade_coneOnePoint B)).Iic_eq]
  induction hW with
  | point x hx => exact hpoint x hx
  | atom t hround hbdry ih =>
    rw [LowerSet.krullDim_Iic] at hd
    have ht : grade ℕ t ≤ 1 := by exact_mod_cast hd
    rcases Nat.lt_or_ge (grade ℕ t) 1 with ht0 | ht1
    · exact hpoint t (grade_eq_zero_iff.1 (by omega))
    · have ht1 : grade ℕ t = 1 := by omega
      refine ⟨fun h => ?_, fun h => absurd h (boundary_closure_zero_false_ne_coneOnePoint B ht1)⟩
      rw [eq_coneOneEdge_of_boundary_eq B ht1 h]
      exact closure_coneOneEdge_subset B
  | paste k V W U hpaste hV hW hk ihV ihW =>
    have hdV := (LowerSet.krullDim_mono hpaste.left_le).trans hd
    have hdW := (LowerSet.krullDim_mono hpaste.right_le).trans hd
    have hk0 : k = 0 := by
      have h1 : (k : WithBot ℕ∞) < 1 := (hk.trans_le (min_le_left _ _)).trans_le hdV
      have : k < 1 := by exact_mod_cast h1
      omega
    subst hk0
    obtain ⟨v, hvmin, hv⟩ := exists_boundary_zero_eq_Iic hV true
    have hvV : v ∈ V := boundary_le _ 0 true (hv ▸ LowerSet.mem_Iic_iff.2 le_rfl)
    have hWs : (cone B 1).ogp.boundary W 0 false = .Iic v :=
      hpaste.inf_eq_input.symm.trans (hpaste.inf_eq_output.trans hv)
    rw [hpaste.boundary_input, ← hpaste.sup_eq, LowerSet.coe_sup]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hVs := (ihV hdV).1 h
      have hv' : v = coneOneOutputVertex B ∨ v = coneOnePoint B := by
        have := hVs hvV
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
        rcases this with h' | h' | h'
        · exact Or.inl h'
        · exact Or.inr h'
        · have := grade_coneOneEdge B
          rw [← h', grade_eq_zero_iff.2 hvmin] at this
          omega
      refine Set.union_subset hVs ?_
      rcases hv' with rfl | rfl
      · exact (ihW hdW).1 hWs
      · exact ((ihW hdW).2 hWs).trans (by simp)
    · have hVs := (ihV hdV).2 h
      have hv' : v = coneOnePoint B := Set.mem_singleton_iff.1 (hVs hvV)
      subst hv'
      exact Set.union_subset hVs ((ihW hdW).2 hWs)

def coneOneBase : (cone B 1).ogp := coneIncl B 1 B.top

theorem coneCoord_coneOneBase : coneCoord B 1 (coneOneBase B) = ((B.top : WithBot _), ∅) :=
  coneCoord_coneIncl B 1 _

theorem coneOneBase_covBy : coneOneBase B ⋖ (cone B 1).top := by
  refine GradeOrder.covBy_of_le_of_grade_eq_add_one ((cone B 1).le_top _) ?_
  have h₁ := grade_cone_add_one B 1 (cone B 1).top
  have h₂ := grade_cone_add_one B 1 (coneOneBase B)
  rw [coneCoord_top, Finset.card_fin] at h₁
  rw [coneCoord_coneOneBase, Finset.card_empty] at h₂
  dsimp only at h₁ h₂
  omega

def coneOneHornData : AtomicHornData :=
  atomicHornDataOfCovBy (cone B 1) (coneOneBase B) (coneOneBase_covBy B)

def coneOneMarking : Set (cone B 1).ogp :=
  {a ∈ ((cone B 1).isRewritableSubmolecule_Iic_of_mem_faces
      (mem_faceSet_top_of_isRewritableSubmolecule (coneOneHornData B).toHornData rfl)).hornSet
      (cone B 1).isMolecule (cone B 1).isAtom.isRound |
    1 < grade ℕ a ∨ a = coneOneEdge B}

theorem mem_coneOneMarking_of_isStagedPasting (hB : 1 ≤ B.dimension) {α : Bool}
    {L R M : ℕ → LowerSet (cone B 1).ogp}
    (hs : (cone B 1).ogp.IsStagedPasting ((cone B 1).dimension - 1) (.Iic (coneOneBase B))
      L R M)
    (hMn : M ((cone B 1).dimension - 1) = (cone B 1).ogp.bdry ⊤ α) :
    ∀ i < (cone B 1).dimension - 1, ∀ y ∈ L (i + 1) ⊔ R (i + 1),
      grade ℕ y = i + 1 → y ∈ coneOneMarking B := by
  have hdU : (cone B 1).dimension = B.dimension + 1 := dimension_cone B 1
  intro i hi y hy hyd
  have hyx : y ∉ LowerSet.Iic (coneOneBase B) := hs.notMem_of_mem_piece hi hy (by omega)
  have hyM : y ∈ M ((cone B 1).dimension - 1) :=
    hs.stage_le (i + 1) _ hi le_rfl (hs.left_sup_right_le_stage hi hy)
  rw [hMn] at hyM
  refine ⟨⟨bdry_le_bdryFull ⊤ α hyM, fun hyi => hyx hyi.1⟩, ?_⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · refine Or.inr ?_
    have hcl : ∀ β, ((cone B 1).ogp.boundary (.Iic (coneOneBase B)) 0 β : Set (cone B 1).ogp) =
        coneIncl B 1 '' (B.ogp.boundary ⊤ 0 β : Set B.ogp) := by
      intro β
      change ((cone B 1).ogp.boundary (.Iic (coneIncl B 1 B.top)) 0 β : Set (cone B 1).ogp) = _
      rw [← (Atom.isMap (coneIncl B 1)).image_boundary, B.Iic_top]
    have hM1 : ∀ β, (cone B 1).ogp.boundary (M 1) 0 β = (cone B 1).ogp.boundary ⊤ 0 β := by
      intro β
      rw [← boundary_stage_zero_eq hs β _ (by omega) le_rfl, hMn,
        (cone B 1).bdry_top_eq_boundary (by omega) α,
        (cone B 1).isMolecule.isGlobular 0 ((cone B 1).dimension - 1) (by omega) β α]
    have p₁ := (hs.stage_succ 0 (by omega)).1
    have p₂ := (hs.stage_succ 0 (by omega)).2
    rcases LowerSet.mem_sup_iff.1 hy with hyL | hyR
    · have hL1 : krullDim (L (0 + 1)) = 0 := by
        refine krullDim_eq_zero_of_boundary_zero_eq (hs.isMoleculeIn_left 0 (by omega)).1 ?_
        rw [← p₁.boundary_input, ← p₂.boundary_input, hM1, ← p₁.inf_eq_output, p₁.inf_eq_input,
          hs.stage_zero]
        refine SetLike.coe_injective ?_
        rw [hcl, ← (cone B 1).Iic_top, boundary_closure_top_zero_false_cone, B.Iic_top]
      have h1 : krullDim (LowerSet.Iic y) ≤ krullDim (L (0 + 1)) :=
        LowerSet.krullDim_mono (LowerSet.Iic_le.2 hyL)
      rw [LowerSet.krullDim_Iic, hL1, hyd] at h1
      have : (0 + 1 : ℕ) ≤ 0 := by exact_mod_cast h1
      omega
    · have hR1 : (cone B 1).ogp.boundary (R 1) 0 false = .Iic (coneOneOutputVertex B) := by
        rw [← p₂.inf_eq_input, p₂.inf_eq_output, p₁.boundary_output, hs.stage_zero]
        refine SetLike.coe_injective ?_
        rw [hcl, boundary_univ_zero_true_eq_singleton, Set.image_singleton, LowerSet.coe_Iic,
          (grade_eq_zero_iff.1 (grade_coneOneOutputVertex B)).Iic_eq]
        rfl
      have hsub := (subset_of_isMoleculeIn_cone_one B (hs.isMoleculeIn_right 0 (by omega)).1
        (hs.isMoleculeIn_right 0 (by omega)).2).1 hR1 hyR
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hsub
      rcases hsub with h | h | h
      · rw [h, grade_coneOneOutputVertex] at hyd
        omega
      · rw [h, grade_coneOnePoint] at hyd
        omega
      · exact h
  · exact Or.inl (by omega)

theorem exists_isStagedPasting_cone_one :
    ∃ L R M : ℕ → LowerSet (cone B 1).ogp,
      (cone B 1).ogp.IsStagedPasting ((cone B 1).dimension - 1) (.Iic (coneOneBase B)) L R M ∧
      M ((cone B 1).dimension - 1) = (cone B 1).ogp.bdry ⊤ (coneOneHornData B).side := by
  have hV := (coneOneHornData B).isRewritableSubmolecule_boundary
  obtain ⟨L, R, M, hs, hMn⟩ := exists_isStagedPasting_of_isSubmoleculeOf hV.isSubmoleculeOf
    ((cone B 1).dimension - 1) (krullDim_boundary_le _ _ _)
  exact ⟨L, R, M, hs, hMn.trans
    ((cone B 1).bdry_top_eq_boundary (coneOneHornData B).positive _).symm⟩

noncomputable def coneOneMarkedHorn (hB : 1 ≤ B.dimension) : MarkedHornData :=
  MarkedHornData.ofStaged (cone B 1) (coneOneHornData B).positive (coneOneHornData B).side
    (coneOneBase B)
    (mem_faceSet_top_of_isRewritableSubmolecule (coneOneHornData B).toHornData rfl)
    (fun a => 1 < grade ℕ a ∨ a = coneOneEdge B)
    (fun a ha => ha.elim (fun h => by omega) fun h => by
      rw [h, grade_coneOneEdge]
      exact Nat.one_pos)
    (exists_isStagedPasting_cone_one B).choose
    (exists_isStagedPasting_cone_one B).choose_spec.choose
    (exists_isStagedPasting_cone_one B).choose_spec.choose_spec.choose
    (exists_isStagedPasting_cone_one B).choose_spec.choose_spec.choose_spec.1
    (exists_isStagedPasting_cone_one B).choose_spec.choose_spec.choose_spec.2
    fun i hi y hy hyd => (mem_coneOneMarking_of_isStagedPasting B hB
      (exists_isStagedPasting_cone_one B).choose_spec.choose_spec.choose_spec.1
      (exists_isStagedPasting_cone_one B).choose_spec.choose_spec.choose_spec.2 i hi y hy hyd).2

end ConeOne

namespace CoherentContraction

variable {B : Atom} {X : DiagSet.{u}} (C : CoherentContraction B X)

def IsExt (c : AugmentedSimplexCategory) (x : X.obj (op (cone B (card c)))) : Prop :=
  ∃ (c' : AugmentedSimplexCategory) (θ : c ⟶ WithInitial.of ⦋0⦌ ⊗ c')
    (w : X.obj (op (cone B (card c')))), IsIso θ ∧
      X.map (coneHom B (toOrderHom θ)).op (C.ext c' w) = x

structure IsFree (c : AugmentedSimplexCategory) (x : X.obj (op (cone B (card c)))) : Prop where
  not_mem : x ∉ (coreFiltration (B.dimension - 1) X).obj (op (cone B (card c)))
  isNondegenerate : EZCategory.IsNondegenerate X x
  not_isExt : ¬ C.IsExt c x

theorem ext_not_mem {c : AugmentedSimplexCategory} {x : X.obj (op (cone B (card c)))}
    (hx : x ∉ (coreFiltration (B.dimension - 1) X).obj (op (cone B (card c)))) :
    C.ext c x ∉ (coreFiltration (B.dimension - 1) X).obj
      (op (cone B (card (WithInitial.of ⦋0⦌ ⊗ c)))) := fun h => hx (by
  rw [← C.map_coneHom_inr_ext c x]
  exact (coreFiltration _ X).map _ h)

theorem isNondegenerate_ext (hB0 : 0 < B.dimension) {c : AugmentedSimplexCategory}
    {x : X.obj (op (cone B (card c)))} (hx : C.IsFree c x) :
    EZCategory.IsNondegenerate X (C.ext c x) := by
  by_contra hnd
  obtain ⟨c', σ, u, hcard, hσu⟩ := exists_card_lt_map_coneHom_eq hB0 (C.ext_not_mem hx.not_mem) hnd
  have hxu : X.map (coneHom B (toOrderHom (inr (WithInitial.of ⦋0⦌) c ≫ σ))).op u = x := by
    rw [coneHom_toOrderHom_comp, op_comp, Functor.map_comp_apply, hσu, C.map_coneHom_inr_ext]
  by_cases hinj : Function.Injective (toFun (inr (WithInitial.of ⦋0⦌) c ≫ σ))
  · have hc₁ : card c ≤ card c' := by
      have := Fintype.card_le_of_injective _ hinj
      simpa only [Fintype.card_fin] using this
    have hc₂ := card_tensorObj (WithInitial.of ⦋0⦌) c
    change _ = 1 + _ at hc₂
    obtain rfl : c = c' := AugmentedSimplexCategory.card_injective (by omega)
    have hid := eq_id_of_injective _ hinj
    rw [hid, toOrderHom_id, coneHom_id, op_id, Functor.map_id_apply] at hxu
    rw [hxu] at hσu
    have hσ₁ : ∀ i : Fin (card c), (toFun σ (toFun (inr (WithInitial.of ⦋0⦌) c) i)).val = i.val :=
      fun i => by rw [← toFun_comp_apply, hid, toFun_id]
    obtain ⟨c₀, hc₀⟩ : ∃ c₀ : AugmentedSimplexCategory, card c₀ + 1 = card c := by
      rcases Nat.eq_zero_or_pos (card c) with h0 | hpos
      · exfalso
        have := (toFun σ ⟨0, by omega⟩).isLt
        omega
      · obtain ⟨c₀, h⟩ := AugmentedSimplexCategory.exists_card_eq (card c - 1)
        exact ⟨c₀, by omega⟩
    have hw : WithInitial.of ⦋0⦌ ⊗ c₀ = c := AugmentedSimplexCategory.card_injective (by
      rw [card_tensorObj]
      change 1 + _ = _
      omega)
    let θ : c₀ ⟶ c := inr (WithInitial.of ⦋0⦌) c₀ ≫ eqToHom hw
    have hθσ : WithInitial.of ⦋0⦌ ◁ θ ≫ σ = eqToHom hw := by
      refine toFun_injective (funext fun i => Fin.ext ?_)
      rw [toFun_comp_apply, val_toFun_eqToHom]
      rcases Nat.eq_zero_or_pos i.val with h0 | hpos
      · have h₀ := AugmentedSimplexCategory.val_toFun_whiskerLeft_of_eq_zero θ i h0
        have hpos1 : 1 < card (WithInitial.of ⦋0⦌ ⊗ c) := by omega
        have hm := monotone_toFun σ (show toFun (WithInitial.of ⦋0⦌ ◁ θ) i ≤
          toFun (inr (WithInitial.of ⦋0⦌) c) ⟨0, by omega⟩ by
            rw [Fin.le_iff_val_le_val, h₀]
            exact Nat.zero_le _)
        have h0' : (toFun σ (toFun (inr (WithInitial.of ⦋0⦌) c) ⟨0, by omega⟩)).val = 0 :=
          hσ₁ ⟨0, by omega⟩
        have hm' : (toFun σ (toFun (WithInitial.of ⦋0⦌ ◁ θ) i)).val ≤
            (toFun σ (toFun (inr (WithInitial.of ⦋0⦌) c) ⟨0, by omega⟩)).val := hm
        omega
      · have h₁ := val_toFun_whiskerLeft_of_ne_zero θ i hpos.ne'
        have hθv : (toFun θ ⟨i.val - 1, by
            have h₂ := card_tensorObj (WithInitial.of ⦋0⦌) c₀
            have := i.isLt
            change _ = 1 + _ at h₂
            omega⟩).val = i.val - 1 + 1 := by
          rw [toFun_comp_apply, val_toFun_eqToHom, val_toFun_inr_zero]
        have hidx : toFun (WithInitial.of ⦋0⦌ ◁ θ) i =
            toFun (inr (WithInitial.of ⦋0⦌) c) ⟨i.val, by
              have h₂ := card_tensorObj (WithInitial.of ⦋0⦌) c₀
              have := i.isLt
              change _ = 1 + _ at h₂
              omega⟩ := Fin.ext (by
          rw [h₁, hθv, val_toFun_inr_zero]
          change i.val - 1 + 1 + 1 = i.val + 1
          omega)
        rw [hidx, hσ₁]
    refine hx.not_isExt ⟨c₀, eqToHom hw.symm, X.map (coneHom B (toOrderHom θ)).op x,
      inferInstance, ?_⟩
    rw [← C.map_coneHom_whiskerLeft_ext, ← hσu, ← Functor.map_comp_apply, ← op_comp,
      ← Functor.map_comp_apply, ← op_comp,
      ← coneHom_toOrderHom_comp, ← coneHom_toOrderHom_comp, Category.assoc, hθσ,
      eqToHom_trans, eqToHom_refl, toOrderHom_id, coneHom_id, op_id, Functor.map_id_apply]
  · exact not_isNondegenerate_map_coneHom B _ hinj u (hxu ▸ hx.isNondegenerate)

theorem isFree_or_exists_isFree (hB0 : 0 < B.dimension) {c : AugmentedSimplexCategory}
    {x : X.obj (op (cone B (card c)))}
    (hx : x ∉ (coreFiltration (B.dimension - 1) X).obj (op (cone B (card c))))
    (hnd : EZCategory.IsNondegenerate X x) :
    C.IsFree c x ∨ ∃ (c' : AugmentedSimplexCategory) (θ : c ⟶ WithInitial.of ⦋0⦌ ⊗ c')
      (w : X.obj (op (cone B (card c')))), IsIso θ ∧ C.IsFree c' w ∧
        X.map (coneHom B (toOrderHom θ)).op (C.ext c' w) = x := by
  by_cases hext : C.IsExt c x
  · obtain ⟨c', θ, w, hθ, rfl⟩ := hext
    have hcθ : card c = card (WithInitial.of ⦋0⦌ ⊗ c') := by
      have h₁ := Fintype.card_le_of_injective _ (injective_toFun_of_isIso θ)
      have h₂ := Fintype.card_le_of_surjective _ (surjective_toFun_of_isIso θ)
      simp only [Fintype.card_fin] at h₁ h₂
      omega
    have hw : w ∉ (coreFiltration (B.dimension - 1) X).obj (op (cone B (card c'))) :=
      fun h => hx ((coreFiltration _ X).map _ (C.ext_mem_coreFiltration c' h))
    refine Or.inr ⟨c', θ, w, hθ, ⟨hw, ?_, ?_⟩, rfl⟩
    · by_contra hwd
      obtain ⟨c'', σ, u, hcard, rfl⟩ := exists_card_lt_map_coneHom_eq hB0 hw hwd
      refine not_isNondegenerate_map_coneHom B (θ ≫ WithInitial.of ⦋0⦌ ◁ σ)
        (not_injective_toFun_of_card_lt _ ?_) (C.ext c'' u) ?_
      · rw [hcθ, card_tensorObj, card_tensorObj]
        omega
      · rw [coneHom_toOrderHom_comp, op_comp, Functor.map_comp_apply,
          C.map_coneHom_whiskerLeft_ext]
        exact hnd
    · rintro ⟨c'', θ', w', hθ', rfl⟩
      refine not_isNondegenerate_map_coneHom B (θ ≫ WithInitial.of ⦋0⦌ ◁ θ' ≫
        ((α_ (WithInitial.of ⦋0⦌) (WithInitial.of ⦋0⦌) c'').inv ≫ zeroMul ▷ c'')) ?_
        (C.ext c'' w') ?_
      · intro hinj
        have hsurj := surjective_toFun_of_isIso (θ ≫ WithInitial.of ⦋0⦌ ◁ θ')
        have hc2 : 2 ≤ card (WithInitial.of ⦋0⦌ ⊗ (WithInitial.of ⦋0⦌ ⊗ c'')) := by
          rw [card_tensorObj, card_tensorObj]
          change 2 ≤ 1 + (1 + _)
          omega
        obtain ⟨i, hi⟩ := hsurj ⟨0, by omega⟩
        obtain ⟨j, hj⟩ := hsurj ⟨1, by omega⟩
        have e : ∀ k, toFun (θ ≫ WithInitial.of ⦋0⦌ ◁ θ' ≫
            ((α_ (WithInitial.of ⦋0⦌) (WithInitial.of ⦋0⦌) c'').inv ≫ zeroMul ▷ c'')) k =
            toFun ((α_ (WithInitial.of ⦋0⦌) (WithInitial.of ⦋0⦌) c'').inv ≫ zeroMul ▷ c'')
              (toFun (θ ≫ WithInitial.of ⦋0⦌ ◁ θ') k) := fun k => by
          rw [← Category.assoc]
          exact toFun_comp_apply _ _ _
        have hij := hinj (a₁ := i) (a₂ := j) (by
          rw [e, e, hi, hj]
          refine Fin.ext ?_
          rw [val_toFun_associator_inv_comp_whiskerRight_zeroMul,
            val_toFun_associator_inv_comp_whiskerRight_zeroMul]
          rfl)
        rw [hij, hj] at hi
        exact absurd (congrArg Fin.val hi) (by simp)
      · rw [coneHom_toOrderHom_comp, coneHom_toOrderHom_comp, op_comp, Functor.map_comp_apply,
          op_comp, Functor.map_comp_apply, C.map_coneHom_zeroMul_ext,
          C.map_coneHom_whiskerLeft_ext]
        exact hnd
  · exact Or.inl ⟨hx, hnd, hext⟩

end CoherentContraction

end Atoms.Diagrammatic
