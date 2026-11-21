import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.SliceComposition
import Atoms.Homotopical.Simplicial.EquivalenceZigzag
import Atoms.Homotopical.Simplicial.SliceFinal

open CategoryTheory Limits Simplicial

universe u

namespace SSet

variable {X : SSet.{u}}

noncomputable def vertexPair (x y : X _⦋0⦌) : (Δ[0] ⨿ Δ[0] : SSet.{u}) ⟶ X :=
  coprod.desc (yonedaEquiv.symm x) (yonedaEquiv.symm y)

section Transpose

variable {K : SSet.{u}} {d : K ⟶ X}

private noncomputable def coneTranspose {n : ℕ} (σ : ((slice K).obj (Under.mk d)) _⦋n⦌) :
    join Δ[n] K ⟶ X :=
  (((joinRightUnderAdjunction K).homEquiv _ _).symm (yonedaEquiv.symm σ)).right

private lemma joinInclRight_comp_coneTranspose {n : ℕ}
    (σ : ((slice K).obj (Under.mk d)) _⦋n⦌) :
    joinInclRight Δ[n] K ≫ coneTranspose σ = d :=
  Under.w (((joinRightUnderAdjunction K).homEquiv _ _).symm (yonedaEquiv.symm σ))

private lemma joinInclLeft_comp_coneTranspose {n : ℕ}
    (σ : ((slice K).obj (Under.mk d)) _⦋n⦌) :
    joinInclLeft Δ[n] K ≫ coneTranspose σ = yonedaEquiv.symm ((sliceπ (Under.mk d)).app _ σ) := by
  rw [coneTranspose, ← comp_sliceπ, yonedaEquiv_symm_comp]

private lemma coneTranspose_δ {n : ℕ} (σ : ((slice K).obj (Under.mk d)) _⦋n + 1⦌)
    (j : Fin (n + 2)) :
    coneTranspose (((slice K).obj (Under.mk d)).δ j σ) =
      joinMap (stdSimplex.δ j) (𝟙 K) ≫ coneTranspose σ := by
  rw [coneTranspose, ← stdSimplex.δ_comp_yonedaEquiv_symm,
    Adjunction.homEquiv_naturality_left_symm, Under.comp_right]
  rfl

private noncomputable def coneOfTranspose {n : ℕ} (φ : join Δ[n] K ⟶ X)
    (hφ : joinInclRight Δ[n] K ≫ φ = d) : ((slice K).obj (Under.mk d)) _⦋n⦌ :=
  yonedaEquiv ((joinRightUnderAdjunction K).homEquiv _ _
    (Under.homMk φ hφ : (joinRightUnder K).obj Δ[n] ⟶ Under.mk d))

private lemma coneTranspose_coneOfTranspose {n : ℕ} (φ : join Δ[n] K ⟶ X)
    (hφ : joinInclRight Δ[n] K ≫ φ = d) :
    coneTranspose (coneOfTranspose φ hφ) = φ := by
  rw [coneTranspose, coneOfTranspose, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rfl

private lemma coneTranspose_injective {n : ℕ} {σ σ' : ((slice K).obj (Under.mk d)) _⦋n⦌}
    (h : coneTranspose σ = coneTranspose σ') : σ = σ' :=
  yonedaEquiv.symm.injective
    (((joinRightUnderAdjunction K).homEquiv _ _).symm.injective (Under.UnderMorphism.ext h))

private noncomputable def legSimplex {n : ℕ} (σ : ((slice K).obj (Under.mk d)) _⦋n⦌)
    (k : Δ[0] ⟶ K) : X _⦋n + 1⦌ :=
  yonedaEquiv ((stdSimplexJoinIso n 0).inv ≫ joinMap (𝟙 Δ[n]) k ≫ coneTranspose σ)

private lemma joinInclLeft_comp_stdSimplexJoinIso_hom_eq_δ_last (n : ℕ) :
    joinInclLeft Δ[n] Δ[0] ≫ (stdSimplexJoinIso.{u} n 0).hom = stdSimplex.δ (Fin.last (n + 1)) :=
  (joinInclLeft_comp_stdSimplexJoinIso_hom n 0).trans
    (congrArg stdSimplex.map (AugmentedSimplexCategory.inl'_eq_δ_last n))

private lemma δ_last_legSimplex {n : ℕ} (σ : ((slice K).obj (Under.mk d)) _⦋n⦌)
    (k : Δ[0] ⟶ K) :
    X.δ (Fin.last (n + 1)) (legSimplex σ k) = (sliceπ (Under.mk d)).app _ σ := by
  have h : stdSimplex.δ (Fin.last (n + 1)) ≫ (stdSimplexJoinIso.{u} n 0).inv =
      joinInclLeft Δ[n] Δ[0] := by
    rw [Iso.comp_inv_eq, joinInclLeft_comp_stdSimplexJoinIso_hom_eq_δ_last]
  rw [legSimplex, ← stdSimplex.yonedaEquiv_δ_comp, reassoc_of% h,
    joinInclLeft_comp_joinMap_assoc, Category.id_comp, joinInclLeft_comp_coneTranspose,
    Equiv.apply_symm_apply]

private lemma joinInclRight_comp_legSimplex {n : ℕ} (σ : ((slice K).obj (Under.mk d)) _⦋n⦌)
    (k : Δ[0] ⟶ K) :
    joinInclRight Δ[n] Δ[0] ≫ (stdSimplexJoinIso n 0).hom ≫ yonedaEquiv.symm (legSimplex σ k) =
      k ≫ d := by
  rw [legSimplex, Equiv.symm_apply_apply, Iso.hom_inv_id_assoc, joinInclRight_comp_joinMap_assoc,
    joinInclRight_comp_coneTranspose]

private lemma joinMap_δ_comp_stdSimplexJoinIso_hom (j : Fin 2) :
    joinMap (stdSimplex.δ j) (𝟙 Δ[0]) ≫ (stdSimplexJoinIso.{u} 1 0).hom =
      (stdSimplexJoinIso 0 0).hom ≫ stdSimplex.δ j.castSucc := by
  have h : AugmentedSimplexCategory.tensorHomOf (SimplexCategory.δ j) (𝟙 ⦋0⦌) =
      SimplexCategory.δ j.castSucc := by
    ext i
    fin_cases j <;> fin_cases i <;> rfl
  have e := joinMap_stdSimplex_map_comp_stdSimplexJoinIso_hom.{u} (SimplexCategory.δ j) (𝟙 ⦋0⦌)
  have e' : stdSimplex.{u}.map (𝟙 ⦋0⦌) = 𝟙 Δ[0] := stdSimplex.map_id _
  rw [h, e'] at e
  exact e

private lemma joinInclRight_comp_stdSimplexJoinIso_hom_comp_zero (τ : X _⦋1⦌) :
    joinInclRight Δ[0] Δ[0] ≫ (stdSimplexJoinIso 0 0).hom ≫ yonedaEquiv.symm τ =
      yonedaEquiv.symm (X.δ 0 τ) := by
  have h : joinInclRight Δ[0] Δ[0] ≫ (stdSimplexJoinIso.{u} 0 0).hom = stdSimplex.δ 0 :=
    (joinInclRight_comp_stdSimplexJoinIso_hom 0 0).trans (congrArg stdSimplex.map (by
      ext i
      fin_cases i
      rfl))
  rw [reassoc_of% h, stdSimplex.δ_comp_yonedaEquiv_symm]

private lemma joinInclRight_comp_stdSimplexJoinIso_hom_comp_one (τ : X _⦋2⦌) :
    joinInclRight Δ[1] Δ[0] ≫ (stdSimplexJoinIso 1 0).hom ≫ yonedaEquiv.symm τ =
      joinInclRight Δ[0] Δ[0] ≫ (stdSimplexJoinIso 0 0).hom ≫ yonedaEquiv.symm (X.δ 0 τ) := by
  have h := joinMap_δ_comp_stdSimplexJoinIso_hom.{u} 0
  have h' := joinInclRight_comp_joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 (Δ[0] : SSet.{u}))
  rw [Category.id_comp] at h'
  rw [← stdSimplex.δ_comp_yonedaEquiv_symm, ← h', Category.assoc, reassoc_of% h]
  rfl

private lemma δ_castSucc_legSimplex (ε : ((slice K).obj (Under.mk d)) _⦋1⦌) (j : Fin 2)
    (k : Δ[0] ⟶ K) :
    X.δ j.castSucc (legSimplex ε k) = legSimplex (((slice K).obj (Under.mk d)).δ j ε) k := by
  have h : stdSimplex.δ j.castSucc ≫ (stdSimplexJoinIso.{u} 1 0).inv =
      (stdSimplexJoinIso 0 0).inv ≫ joinMap (stdSimplex.δ j) (𝟙 Δ[0]) := by
    rw [Iso.comp_inv_eq, Category.assoc, joinMap_δ_comp_stdSimplexJoinIso_hom,
      Iso.inv_hom_id_assoc]
  rw [legSimplex, legSimplex, ← stdSimplex.yonedaEquiv_δ_comp, reassoc_of% h, coneTranspose_δ,
    joinMap_comp_joinMap_assoc, joinMap_comp_joinMap_assoc, Category.id_comp, Category.comp_id,
    Category.id_comp, Category.comp_id]

private lemma δ_zero_legSimplex (σ : ((slice K).obj (Under.mk d)) _⦋0⦌) (k : Δ[0] ⟶ K) :
    X.δ 0 (legSimplex σ k) = yonedaEquiv (k ≫ d) := by
  rw [← joinInclRight_comp_legSimplex σ k, joinInclRight_comp_stdSimplexJoinIso_hom_comp_zero,
    Equiv.apply_symm_apply]

private lemma nonempty_compStruct_legSimplex {σ σ' : ((slice K).obj (Under.mk d)) _⦋0⦌}
    (ε : Edge σ σ') (k : Δ[0] ⟶ K) {z : X _⦋0⦌} {e : Edge ((sliceπ (Under.mk d)).app _ σ') z}
    {e' : Edge ((sliceπ (Under.mk d)).app _ σ) z} (he : e.edge = legSimplex σ' k)
    (he' : e'.edge = legSimplex σ k) :
    Nonempty (Edge.CompStruct (ε.map (sliceπ (Under.mk d))) e e') :=
  ⟨Edge.CompStruct.mk (legSimplex ε.edge k) (δ_last_legSimplex ε.edge k)
    ((δ_castSucc_legSimplex ε.edge 0 k).trans (by rw [ε.tgt_eq, he]))
    ((δ_castSucc_legSimplex ε.edge 1 k).trans (by rw [ε.src_eq, he']))⟩

end Transpose

section Pair

private lemma isPushout_joinMap_coprod (n : ℕ) :
    IsPushout (joinMap (𝟙 Δ[n]) (⊥ : (Δ[0] : SSet.{u}).Subcomplex).ι)
      (joinMap (𝟙 Δ[n]) (⊥ : (Δ[0] : SSet.{u}).Subcomplex).ι)
      (joinMap (𝟙 Δ[n]) (coprod.inl : (Δ[0] : SSet.{u}) ⟶ Δ[0] ⨿ Δ[0]))
      (joinMap (𝟙 Δ[n]) coprod.inr) :=
  have : PreservesColimitsOfSize.{0, 0} (joinLeftUnder (Δ[n] : SSet.{u})) :=
    preservesColimitsOfSize_shrink _
  isPushout_bot_ι_coprod.map (joinLeftUnder (Δ[n] : SSet.{u}) ⋙ Under.forget Δ[n])

private lemma joinMap_bot_ι_comp_eq {n : ℕ} {a b : join Δ[n] Δ[0] ⟶ X}
    (h : joinInclLeft Δ[n] Δ[0] ≫ a = joinInclLeft Δ[n] Δ[0] ≫ b) :
    joinMap (𝟙 Δ[n]) (⊥ : (Δ[0] : SSet.{u}).Subcomplex).ι ≫ a =
      joinMap (𝟙 Δ[n]) (⊥ : (Δ[0] : SSet.{u}).Subcomplex).ι ≫ b := by
  have : IsIso (joinInclLeft Δ[n] ((⊥ : (Δ[0] : SSet.{u}).Subcomplex) : SSet.{u})) :=
    isIso_joinInclLeft_of_isEmpty _ _
  rw [← cancel_epi (joinInclLeft Δ[n] ((⊥ : (Δ[0] : SSet.{u}).Subcomplex) : SSet.{u})),
    joinInclLeft_comp_joinMap_assoc, joinInclLeft_comp_joinMap_assoc, Category.id_comp]
  exact h

variable {d : (Δ[0] ⨿ Δ[0] : SSet.{u}) ⟶ X}

private lemma exists_legSimplex_eq {n : ℕ} (τ₁ τ₂ : X _⦋n + 1⦌)
    (hτ : X.δ (Fin.last (n + 1)) τ₁ = X.δ (Fin.last (n + 1)) τ₂)
    (h₁ : joinInclRight Δ[n] Δ[0] ≫ (stdSimplexJoinIso n 0).hom ≫ yonedaEquiv.symm τ₁ =
      coprod.inl ≫ d)
    (h₂ : joinInclRight Δ[n] Δ[0] ≫ (stdSimplexJoinIso n 0).hom ≫ yonedaEquiv.symm τ₂ =
      coprod.inr ≫ d) :
    ∃ σ : ((slice _).obj (Under.mk d)) _⦋n⦌, legSimplex σ coprod.inl = τ₁ ∧
      legSimplex σ coprod.inr = τ₂ ∧ (sliceπ (Under.mk d)).app _ σ = X.δ (Fin.last (n + 1)) τ₁ := by
  obtain ⟨φ, hφ₁, hφ₂⟩ := (isPushout_joinMap_coprod n).exists_desc
    ((stdSimplexJoinIso n 0).hom ≫ yonedaEquiv.symm τ₁)
    ((stdSimplexJoinIso n 0).hom ≫ yonedaEquiv.symm τ₂) (joinMap_bot_ι_comp_eq (by
      rw [reassoc_of% joinInclLeft_comp_stdSimplexJoinIso_hom_eq_δ_last,
        reassoc_of% joinInclLeft_comp_stdSimplexJoinIso_hom_eq_δ_last,
        stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm, hτ]))
  have hφ : joinInclRight Δ[n] _ ≫ φ = d := coprod.hom_ext
    (by rw [← reassoc_of% joinInclRight_comp_joinMap (𝟙 Δ[n]), hφ₁, h₁])
    (by rw [← reassoc_of% joinInclRight_comp_joinMap (𝟙 Δ[n]), hφ₂, h₂])
  have h : legSimplex (coneOfTranspose φ hφ) coprod.inl = τ₁ := by
    rw [legSimplex, coneTranspose_coneOfTranspose, hφ₁, Iso.inv_hom_id_assoc,
      Equiv.apply_symm_apply]
  refine ⟨_, h, ?_, (δ_last_legSimplex (coneOfTranspose φ hφ) coprod.inl).symm.trans (by rw [h])⟩
  rw [legSimplex, coneTranspose_coneOfTranspose, hφ₂, Iso.inv_hom_id_assoc,
    Equiv.apply_symm_apply]

private lemma eq_of_legSimplex_eq {n : ℕ} {σ σ' : ((slice _).obj (Under.mk d)) _⦋n⦌}
    (h₁ : legSimplex σ coprod.inl = legSimplex σ' coprod.inl)
    (h₂ : legSimplex σ coprod.inr = legSimplex σ' coprod.inr) : σ = σ' := by
  have key (k : (Δ[0] : SSet.{u}) ⟶ Δ[0] ⨿ Δ[0]) (hk : legSimplex σ k = legSimplex σ' k) :
      joinMap (𝟙 Δ[n]) k ≫ coneTranspose σ = joinMap (𝟙 Δ[n]) k ≫ coneTranspose σ' := by
    rw [← cancel_epi (stdSimplexJoinIso n 0).inv]
    exact yonedaEquiv.injective hk
  exact coneTranspose_injective ((isPushout_joinMap_coprod n).hom_ext (key _ h₁) (key _ h₂))

end Pair

variable {x y : X _⦋0⦌}

noncomputable def productConeApex (c : ((slice _).obj (Under.mk (vertexPair x y))) _⦋0⦌) :
    X _⦋0⦌ :=
  (sliceπ (Under.mk (vertexPair x y))).app _ c

noncomputable def productConeFst (c : ((slice _).obj (Under.mk (vertexPair x y))) _⦋0⦌) :
    Edge (productConeApex c) x :=
  Edge.mk (legSimplex c coprod.inl) (δ_last_legSimplex c _)
    (by rw [δ_zero_legSimplex, vertexPair, coprod.inl_desc, Equiv.apply_symm_apply])

noncomputable def productConeSnd (c : ((slice _).obj (Under.mk (vertexPair x y))) _⦋0⦌) :
    Edge (productConeApex c) y :=
  Edge.mk (legSimplex c coprod.inr) (δ_last_legSimplex c _)
    (by rw [δ_zero_legSimplex, vertexPair, coprod.inr_desc, Equiv.apply_symm_apply])

theorem exists_productCone {w : X _⦋0⦌} (f : Edge w x) (g : Edge w y) :
    ∃ c : ((slice _).obj (Under.mk (vertexPair x y))) _⦋0⦌, productConeApex c = w ∧
      (productConeFst c).edge = f.edge ∧ (productConeSnd c).edge = g.edge := by
  obtain ⟨c, hf, hg, hc⟩ := exists_legSimplex_eq (d := vertexPair x y) f.edge g.edge
    (f.src_eq.trans g.src_eq.symm)
    (by rw [joinInclRight_comp_stdSimplexJoinIso_hom_comp_zero, f.tgt_eq, vertexPair,
      coprod.inl_desc])
    (by rw [joinInclRight_comp_stdSimplexJoinIso_hom_comp_zero, g.tgt_eq, vertexPair,
      coprod.inr_desc])
  exact ⟨c, hc.trans f.src_eq, hf, hg⟩

def IsProductCone (c : ((slice _).obj (Under.mk (vertexPair x y))) _⦋0⦌) : Prop :=
  IsFinal c

private lemma exists_comp_homMk_eq [X.Quasicategory]
    {c : ((slice _).obj (Under.mk (vertexPair x y))) _⦋0⦌} (hc : IsProductCone c) {w : X _⦋0⦌}
    (f : Edge w x) (g : Edge w y) :
    ∃ m : Truncated.HomotopyCategory.mk (V := (truncation 2).obj X) w ⟶
        Truncated.HomotopyCategory.mk (productConeApex c),
      m ≫ Truncated.HomotopyCategory.homMk (productConeFst c) =
          Truncated.HomotopyCategory.homMk f ∧
        m ≫ Truncated.HomotopyCategory.homMk (productConeSnd c) =
          Truncated.HomotopyCategory.homMk g := by
  have := @quasicategory_slice _ (Under.mk (vertexPair x y)) (inferInstanceAs X.Quasicategory)
  obtain ⟨c₀, rfl, hf, hg⟩ := exists_productCone f g
  obtain ⟨ε, -⟩ := Truncated.HomotopyCategory.homMk_surjective
    ((isTerminalOfIsFinal hc).from (Truncated.HomotopyCategory.mk c₀))
  obtain ⟨s₁⟩ := nonempty_compStruct_legSimplex ε coprod.inl (e := productConeFst c) (e' := f)
    rfl hf.symm
  obtain ⟨s₂⟩ := nonempty_compStruct_legSimplex ε coprod.inr (e := productConeSnd c) (e' := g)
    rfl hg.symm
  exact ⟨_, Truncated.HomotopyCategory.homMk_comp_homMk s₁.toTruncated,
    Truncated.HomotopyCategory.homMk_comp_homMk s₂.toTruncated⟩

private lemma nonempty_compStruct_of_homMk_comp_homMk [X.Quasicategory] {a b z : X _⦋0⦌}
    {f : Edge a b} {g : Edge b z} {h : Edge a z}
    (fac : Truncated.HomotopyCategory.homMk (V := (truncation 2).obj X) f ≫
      Truncated.HomotopyCategory.homMk g = Truncated.HomotopyCategory.homMk h) :
    Nonempty (Edge.CompStruct f g h) := by
  obtain ⟨s⟩ := Truncated.Edge.CompStruct.nonempty_iff.2
    ((Truncated.HomotopyCategory₂.equivalence ((truncation 2).obj X)).functor.map_injective
      (by rw [Functor.map_comp]; exact fac) :
      Truncated.HomotopyCategory₂.homMk f.toTruncated ≫
        Truncated.HomotopyCategory₂.homMk g.toTruncated =
          Truncated.HomotopyCategory₂.homMk h.toTruncated)
  exact ⟨.ofTruncated s⟩

private lemma exists_edge_of_compStruct {c : ((slice _).obj (Under.mk (vertexPair x y))) _⦋0⦌}
    {w : X _⦋0⦌} {h : Edge w (productConeApex c)} {f : Edge w x} {g : Edge w y}
    (s₁ : Edge.CompStruct h (productConeFst c) f) (s₂ : Edge.CompStruct h (productConeSnd c) g) :
    ∃ (c₀ : ((slice _).obj (Under.mk (vertexPair x y))) _⦋0⦌) (ε : Edge c₀ c),
      legSimplex c₀ coprod.inl = f.edge ∧ legSimplex c₀ coprod.inr = g.edge ∧
        (sliceπ (Under.mk (vertexPair x y))).app _ ε.edge = h.edge := by
  obtain ⟨ε, hε₁, hε₂, hε⟩ := exists_legSimplex_eq (d := vertexPair x y) s₁.simplex s₂.simplex
    (s₁.d₂.trans s₂.d₂.symm)
    (by rw [joinInclRight_comp_stdSimplexJoinIso_hom_comp_one, s₁.d₀]
        exact joinInclRight_comp_legSimplex c coprod.inl)
    (by rw [joinInclRight_comp_stdSimplexJoinIso_hom_comp_one, s₂.d₀]
        exact joinInclRight_comp_legSimplex c coprod.inr)
  have hl₁ (j : Fin 2) : legSimplex (((slice _).obj _).δ j ε) coprod.inl =
      X.δ j.castSucc s₁.simplex := by
    rw [← δ_castSucc_legSimplex, hε₁]
  have hl₂ (j : Fin 2) : legSimplex (((slice _).obj _).δ j ε) coprod.inr =
      X.δ j.castSucc s₂.simplex := by
    rw [← δ_castSucc_legSimplex, hε₂]
  exact ⟨_, Edge.mk ε rfl (eq_of_legSimplex_eq ((hl₁ 0).trans s₁.d₀) ((hl₂ 0).trans s₂.d₀)),
    (hl₁ 1).trans s₁.d₁, (hl₂ 1).trans s₂.d₁, hε.trans s₁.d₂⟩

private lemma homMk_eq_of_compStruct [X.Quasicategory]
    {c : ((slice _).obj (Under.mk (vertexPair x y))) _⦋0⦌} (hc : IsProductCone c) {w : X _⦋0⦌}
    {h h' : Edge w (productConeApex c)} {f : Edge w x} {g : Edge w y}
    (s₁ : Edge.CompStruct h (productConeFst c) f) (s₂ : Edge.CompStruct h (productConeSnd c) g)
    (s₁' : Edge.CompStruct h' (productConeFst c) f)
    (s₂' : Edge.CompStruct h' (productConeSnd c) g) :
    Truncated.HomotopyCategory.homMk (V := (truncation 2).obj X) h =
      Truncated.HomotopyCategory.homMk h' := by
  have := @quasicategory_slice _ (Under.mk (vertexPair x y)) (inferInstanceAs X.Quasicategory)
  obtain ⟨c₀, ε, hf, hg, hε⟩ := exists_edge_of_compStruct s₁ s₂
  obtain ⟨c₀', ε', hf', hg', hε'⟩ := exists_edge_of_compStruct s₁' s₂'
  obtain rfl : c₀ = c₀' := eq_of_legSimplex_eq (hf.trans hf'.symm) (hg.trans hg'.symm)
  have e := congrArg (Truncated.mapHomotopyCategory
    ((truncation 2).map (sliceπ (Under.mk (vertexPair x y))))).map ((isTerminalOfIsFinal hc).hom_ext
      (Truncated.HomotopyCategory.homMk ε) (Truncated.HomotopyCategory.homMk ε'))
  exact (Arrow.mk_inj _ _).1
    ((Truncated.HomotopyCategory.congr_arrowMk_homMk h.toTruncated
      (ε.toTruncated.map ((truncation 2).map (sliceπ (Under.mk (vertexPair x y))))) hε.symm).trans
      ((congrArg Arrow.mk e).trans (Truncated.HomotopyCategory.congr_arrowMk_homMk
        (ε'.toTruncated.map ((truncation 2).map (sliceπ (Under.mk (vertexPair x y)))))
        h'.toTruncated hε')))

noncomputable def productConeFan (c : ((slice _).obj (Under.mk (vertexPair x y))) _⦋0⦌) :
    BinaryFan (Truncated.HomotopyCategory.mk (V := (truncation 2).obj X) x)
      (Truncated.HomotopyCategory.mk y) :=
  BinaryFan.mk (Truncated.HomotopyCategory.homMk (productConeFst c).toTruncated)
    (Truncated.HomotopyCategory.homMk (productConeSnd c).toTruncated)

private lemma existsUnique_comp_eq [X.Quasicategory]
    {c : ((slice _).obj (Under.mk (vertexPair x y))) _⦋0⦌} (hc : IsProductCone c)
    {T : Truncated.HomotopyCategory ((truncation 2).obj X)}
    (f : T ⟶ Truncated.HomotopyCategory.mk x) (g : T ⟶ Truncated.HomotopyCategory.mk y) :
    ∃! m : T ⟶ (productConeFan c).pt,
      m ≫ (productConeFan c).fst = f ∧ m ≫ (productConeFan c).snd = g := by
  obtain ⟨w, rfl⟩ := Truncated.HomotopyCategory.mk_surjective T
  obtain ⟨f, rfl⟩ := Truncated.HomotopyCategory.homMk_surjective f
  obtain ⟨g, rfl⟩ := Truncated.HomotopyCategory.homMk_surjective g
  obtain ⟨m, hm⟩ := exists_comp_homMk_eq hc (Edge.ofTruncated f) (Edge.ofTruncated g)
  refine ⟨m, hm, fun m' hm' ↦ ?_⟩
  obtain ⟨h, rfl⟩ := Truncated.HomotopyCategory.homMk_surjective m
  obtain ⟨h', rfl⟩ := Truncated.HomotopyCategory.homMk_surjective m'
  obtain ⟨s₁⟩ := nonempty_compStruct_of_homMk_comp_homMk (g := productConeFst c) hm.1
  obtain ⟨s₂⟩ := nonempty_compStruct_of_homMk_comp_homMk (g := productConeSnd c) hm.2
  obtain ⟨s₁'⟩ := nonempty_compStruct_of_homMk_comp_homMk (g := productConeFst c) hm'.1
  obtain ⟨s₂'⟩ := nonempty_compStruct_of_homMk_comp_homMk (g := productConeSnd c) hm'.2
  exact homMk_eq_of_compStruct hc s₁' s₂' s₁ s₂

noncomputable def isLimitProductConeFan [X.Quasicategory]
    {c : ((slice _).obj (Under.mk (vertexPair x y))) _⦋0⦌} (hc : IsProductCone c) :
    IsLimit (productConeFan c) :=
  BinaryFan.IsLimit.mk _ (fun f g ↦ (existsUnique_comp_eq hc f g).exists.choose)
    (fun f g ↦ (existsUnique_comp_eq hc f g).exists.choose_spec.1)
    (fun f g ↦ (existsUnique_comp_eq hc f g).exists.choose_spec.2)
    (fun f g _ hm₁ hm₂ ↦ (existsUnique_comp_eq hc f g).unique ⟨hm₁, hm₂⟩
      (existsUnique_comp_eq hc f g).exists.choose_spec)

theorem hasBinaryProducts_homotopyCategory [X.Quasicategory]
    (h : ∀ x y : X _⦋0⦌, ∃ c : ((slice _).obj (Under.mk (vertexPair x y))) _⦋0⦌,
      IsProductCone c) :
    HasBinaryProducts (Truncated.HomotopyCategory ((truncation 2).obj X)) := by
  have (a b : Truncated.HomotopyCategory ((truncation 2).obj X)) : HasLimit (pair a b) := by
    obtain ⟨x, rfl⟩ := Truncated.HomotopyCategory.mk_surjective a
    obtain ⟨y, rfl⟩ := Truncated.HomotopyCategory.mk_surjective b
    obtain ⟨c, hc⟩ := h x y
    exact ⟨⟨⟨_, isLimitProductConeFan hc⟩⟩⟩
  exact hasBinaryProducts_of_hasLimit_pair _

theorem hasFiniteProducts_homotopyCategory [X.Quasicategory] (h₀ : ∃ ω : X _⦋0⦌, IsFinal ω)
    (h : ∀ x y : X _⦋0⦌, ∃ c : ((slice _).obj (Under.mk (vertexPair x y))) _⦋0⦌,
      IsProductCone c) :
    HasFiniteProducts (Truncated.HomotopyCategory ((truncation 2).obj X)) :=
  have := hasBinaryProducts_homotopyCategory h
  have ⟨_, hω⟩ := h₀
  have := (isTerminalOfIsFinal hω).hasTerminal
  hasFiniteProducts_of_has_binary_and_terminal

open private isIso_homMk_iff_of_edge_eq
  from Atoms.ForMathlib.AlgebraicTopology.Quasicategory.Isofibration in
theorem isoVertices_of_legs [X.Quasicategory]
    {c c' : ((slice _).obj (Under.mk (vertexPair x y))) _⦋0⦌}
    (φ : Truncated.HomotopyCategory.mk (V := (truncation 2).obj X) (productConeApex c) ≅
      Truncated.HomotopyCategory.mk (productConeApex c'))
    (h₁ : φ.hom ≫ Truncated.HomotopyCategory.homMk (productConeFst c') =
      Truncated.HomotopyCategory.homMk (productConeFst c))
    (h₂ : φ.hom ≫ Truncated.HomotopyCategory.homMk (productConeSnd c') =
      Truncated.HomotopyCategory.homMk (productConeSnd c)) :
    IsoVertices c c' := by
  have := @quasicategory_slice _ (Under.mk (vertexPair x y)) (inferInstanceAs X.Quasicategory)
  obtain ⟨h, hh⟩ := Truncated.HomotopyCategory.homMk_surjective φ.hom
  obtain ⟨s₁⟩ := nonempty_compStruct_of_homMk_comp_homMk (f := Edge.ofTruncated h)
    (g := productConeFst c') (h := productConeFst c) (hh.symm ▸ h₁)
  obtain ⟨s₂⟩ := nonempty_compStruct_of_homMk_comp_homMk (f := Edge.ofTruncated h)
    (g := productConeSnd c') (h := productConeSnd c) (hh.symm ▸ h₂)
  obtain ⟨c₀, ε, hf, hg, hε⟩ := exists_edge_of_compStruct s₁ s₂
  obtain rfl : c₀ = c := eq_of_legSimplex_eq hf hg
  have : (Under.mk (vertexPair x y)).right.Quasicategory := ‹X.Quasicategory›
  have hi : IsIso (Truncated.HomotopyCategory.homMk (Edge.ofTruncated h)) :=
    hh ▸ Iso.isIso_hom φ
  have := (isIso_homMk_iff ε).2 (nonempty_invStruct_of_rightFibrations
    (rightFibrations_sliceπ (X := X) (vertexPair x y)) ε ((isIso_homMk_iff _).1
      ((isIso_homMk_iff_of_edge_eq _ _ hε.symm).1 hi)))
  exact ⟨asIso (Truncated.HomotopyCategory.homMk ε)⟩

theorem vertexPair_app_inl (x y : X _⦋0⦌) :
    (vertexPair x y).app _ (yonedaEquiv (coprod.inl : (Δ[0] : SSet.{u}) ⟶ Δ[0] ⨿ Δ[0])) = x := by
  rw [← yonedaEquiv_comp, vertexPair, coprod.inl_desc, Equiv.apply_symm_apply]

theorem vertexPair_app_inr (x y : X _⦋0⦌) :
    (vertexPair x y).app _ (yonedaEquiv (coprod.inr : (Δ[0] : SSet.{u}) ⟶ Δ[0] ⨿ Δ[0])) = y := by
  rw [← yonedaEquiv_comp, vertexPair, coprod.inr_desc, Equiv.apply_symm_apply]

private lemma commaConeLeg_sliceToCommaCone {K : SSet.{u}} {d : K ⟶ X} {k : K _⦋0⦌}
    {z : X _⦋0⦌} (hz : d.app _ k = z) (σ : ((slice K).obj (Under.mk d)) _⦋0⦌) :
    (commaConeLeg hz ((sliceToCommaCone d).app _ σ)).edge = legSimplex σ (yonedaEquiv.symm k) := by
  have h := ihomPointEquiv_sliceToCommaCone_arrow_evalVertex d k (yonedaEquiv.symm σ)
  rw [yonedaEquiv_symm_comp] at h
  exact congrArg yonedaEquiv h

theorem commaConeLeg_sliceToCommaCone_inl
    (c : ((slice _).obj (Under.mk (vertexPair x y))) _⦋0⦌) :
    (commaConeLeg (vertexPair_app_inl x y) ((sliceToCommaCone _).app _ c)).edge =
      (productConeFst c).edge :=
  (commaConeLeg_sliceToCommaCone _ c).trans (by rw [Equiv.symm_apply_apply]; rfl)

theorem commaConeLeg_sliceToCommaCone_inr
    (c : ((slice _).obj (Under.mk (vertexPair x y))) _⦋0⦌) :
    (commaConeLeg (vertexPair_app_inr x y) ((sliceToCommaCone _).app _ c)).edge =
      (productConeSnd c).edge :=
  (commaConeLeg_sliceToCommaCone _ c).trans (by rw [Equiv.symm_apply_apply]; rfl)

open private isIso_homMk_iff_of_edge_eq
  from Atoms.ForMathlib.AlgebraicTopology.Quasicategory.Isofibration in
open modelCategoryJoyal in
theorem isLimitCone_iff_isProductCone_of_legs [X.Quasicategory]
    {v : (commaCone (vertexPair x y)) _⦋0⦌} {c : ((slice _).obj (Under.mk (vertexPair x y))) _⦋0⦌}
    (φ : Truncated.HomotopyCategory.mk (V := (truncation 2).obj X)
      ((commaConeπ (vertexPair x y)).app _ v) ≅ Truncated.HomotopyCategory.mk (productConeApex c))
    (h₁ : φ.hom ≫ Truncated.HomotopyCategory.homMk (productConeFst c) =
      Truncated.HomotopyCategory.homMk (commaConeLeg (vertexPair_app_inl x y) v))
    (h₂ : φ.hom ≫ Truncated.HomotopyCategory.homMk (productConeSnd c) =
      Truncated.HomotopyCategory.homMk (commaConeLeg (vertexPair_app_inr x y) v)) :
    IsLimitCone (vertexPair x y) v ↔ IsProductCone c := by
  have := @quasicategory_slice _ (Under.mk (vertexPair x y)) (inferInstanceAs X.Quasicategory)
  have := weakEquivalence_sliceToCommaCone (vertexPair x y)
  obtain ⟨c', ⟨i⟩⟩ := exists_isoVertices_of_weakEquivalence (sliceToCommaCone _) v
  obtain ⟨e, he⟩ := Truncated.HomotopyCategory.homMk_surjective i.hom
  have hi : IsIso (Truncated.HomotopyCategory.homMk (Edge.ofTruncated e)) := he ▸ Iso.isIso_hom i
  let p : Edge (productConeApex c') ((commaConeπ (vertexPair x y)).app _ v) :=
    Edge.mk ((Edge.ofTruncated e).map (commaConeπ _)).edge
      (((Edge.ofTruncated e).map (commaConeπ _)).src_eq.trans
        (congrArg (fun f ↦ f.app _ c') (sliceToCommaCone_commaConeπ _)))
      ((Edge.ofTruncated e).map (commaConeπ _)).tgt_eq
  have hp : IsIso (Truncated.HomotopyCategory.homMk p) :=
    (isIso_homMk_iff_of_edge_eq ((Edge.ofTruncated e).map (commaConeπ _)) p rfl).1
      (Functor.map_isIso (Truncated.mapHomotopyCategory
        ((truncation 2).map (commaConeπ (vertexPair x y))))
          (Truncated.HomotopyCategory.homMk (Edge.ofTruncated e)))
  have k₁ := homMk_commaConeLeg (vertexPair_app_inl x y) (Edge.ofTruncated e)
    (f := productConeFst c') (p := p) (commaConeLeg_sliceToCommaCone_inl c').symm rfl rfl
  have k₂ := homMk_commaConeLeg (vertexPair_app_inr x y) (Edge.ofTruncated e)
    (f := productConeSnd c') (p := p) (commaConeLeg_sliceToCommaCone_inr c').symm rfl rfl
  have hc : IsoVertices c' c :=
    isoVertices_of_legs (asIso (Truncated.HomotopyCategory.homMk p) ≪≫ φ)
    (by rw [Iso.trans_hom, asIso_hom, Category.assoc, h₁]; exact k₁.symm)
    (by rw [Iso.trans_hom, asIso_hom, Category.assoc, h₂]; exact k₂.symm)
  rw [IsProductCone, ← hc.isFinal_iff, isFinal_iff_isLimitCone_sliceToCommaCone]
  exact (IsoVertices.isFinal_iff ⟨i⟩).symm

def IsCoproductCone
    (c : ((slice _).obj (Under.mk (vertexPair (X := X.op) (opObjEquiv.symm x)
      (opObjEquiv.symm y)))) _⦋0⦌) : Prop :=
  IsProductCone c

theorem hasBinaryCoproducts_homotopyCategory [X.Quasicategory]
    (h : ∀ x y : X _⦋0⦌, ∃ c : ((slice _).obj (Under.mk (vertexPair (X := X.op)
      (opObjEquiv.symm x) (opObjEquiv.symm y)))) _⦋0⦌, IsCoproductCone c) :
    HasBinaryCoproducts (Truncated.HomotopyCategory ((truncation 2).obj X)) := by
  have := hasBinaryProducts_homotopyCategory (X := X.op) fun x y ↦ by
    obtain ⟨x, rfl⟩ := opObjEquiv.symm.surjective x
    obtain ⟨y, rfl⟩ := opObjEquiv.symm.surjective y
    exact h x y
  have : HasBinaryProducts (Truncated.HomotopyCategory ((truncation 2).obj X))ᵒᵖ :=
    Adjunction.hasLimitsOfShape_of_equivalence (Truncated.HomotopyCategory.opEquivalence X).inverse
  exact hasCoproductsOfShape_of_opposite WalkingPair

theorem hasFiniteCoproducts_homotopyCategory [X.Quasicategory]
    (h₀ : ∃ ω : X _⦋0⦌, IsInitialObject ω)
    (h : ∀ x y : X _⦋0⦌, ∃ c : ((slice _).obj (Under.mk (vertexPair (X := X.op)
      (opObjEquiv.symm x) (opObjEquiv.symm y)))) _⦋0⦌, IsCoproductCone c) :
    HasFiniteCoproducts (Truncated.HomotopyCategory ((truncation 2).obj X)) :=
  have := hasBinaryCoproducts_homotopyCategory h
  have ⟨_, hω⟩ := h₀
  have := (isInitialOfIsInitialObject hω).hasInitial
  hasFiniteCoproducts_of_has_binary_and_initial

end SSet
