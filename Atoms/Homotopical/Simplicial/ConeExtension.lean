import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.ConeExtension
import Atoms.Homotopical.Simplicial.CommaLimit
import Atoms.Homotopical.Simplicial.FatJoin
import Atoms.Homotopical.Simplicial.SliceFinal

open CategoryTheory Limits Simplicial Opposite MonoidalCategory MonoidalClosed
  CartesianMonoidalCategory HomotopicalAlgebra MorphismProperty

universe u

namespace SSet

theorem trivialFibration_fiberwiseFinalRes_fatJoin (K X : SSet.{u}) [X.Quasicategory] :
    modelCategoryQuillen.I.rlp
      (fiberwiseFinalRes ((pre (fatJoinInclRight (Δ[0] : SSet.{u}) K)).app X)) := by
  set p := (pre (fatJoinInclRight (Δ[0] : SSet.{u}) K)).app X with hp
  suffices H : ∀ n, HasLiftingProperty (boundary.{u} n).ι (fiberwiseFinalRes p) from
    fun _ _ _ ⟨n⟩ ↦ H n
  intro n
  refine ⟨fun {a b} sq ↦ ?_⟩
  cases n with
  | zero =>
    obtain ⟨ω, hω⟩ := (mem_hasFinalFiberSubcomplex_obj_zero_iff p _).1 (yonedaEquiv b).2
    obtain ⟨e, he, rfl⟩ := exists_fiberVertex_eq p ω
    have hmem := (mem_fiberwiseFinalSubcomplex_obj_zero_iff p e he).2 hω
    refine ⟨⟨⟨yonedaEquiv.symm ⟨e, hmem⟩, boundary.hom_ext₀, ?_⟩⟩⟩
    rw [← cancel_mono (hasFinalFiberSubcomplex p).ι, Category.assoc, fiberwiseFinalRes_ι]
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp]
    exact he
  | succ n =>
    set f₀ := a ≫ (fiberwiseFinalSubcomplex p).ι with hf₀
    set g := b ≫ (hasFinalFiberSubcomplex p).ι with hg
    have hfg : (∂Δ[n + 1]).ι ≫ g = f₀ ≫ p := by
      rw [hf₀, hg, ← Category.assoc, ← sq.w, Category.assoc, fiberwiseFinalRes_ι,
        Category.assoc]
    obtain ⟨H, hH₀, hHp, hHl⟩ := exists_fatCone_homotopy f₀ g hfg
    have hb₁ : yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (Fin.last (n + 1))) ≫ g =
        yonedaEquiv.symm ((f₀ ≫ p).app _ (boundary.lastVertex n)) := by
      rw [← yonedaEquiv_symm_comp, ← hfg, ← lastVertex_ι, Category.assoc]
    have hH₁ : (lift (stdSimplex.isTerminalObj₀.from _ ≫ stdSimplex.δ 0) (𝟙 _) ≫ H) ≫ p =
        stdSimplex.isTerminalObj₀.from _ ≫
          yonedaEquiv.symm ((f₀ ≫ p).app _ (boundary.lastVertex n)) := by
      rw [Category.assoc, hHp, lift_whiskerLeft_assoc, Category.id_comp,
        lift_δ_zero_contractToLast_assoc, hb₁]
    have : InnerFibration
        (pullback.snd p (yonedaEquiv.symm ((f₀ ≫ p).app _ (boundary.lastVertex n)))) :=
      ⟨innerFibrations.of_isPullback (IsPullback.of_hasPullback _ _) (mem_innerFibrations p)⟩
    have := quasicategory_of_innerFibration
      (pullback.snd p (yonedaEquiv.symm ((f₀ ≫ p).app _ (boundary.lastVertex n))))
    set H₁ := pullback.lift _ _ hH₁ with hH₁def
    have hpl : p.app _ (f₀.app _ (boundary.lastVertex n)) =
        (f₀ ≫ p).app _ (boundary.lastVertex n) := rfl
    have hfin := (mem_fiberwiseFinalSubcomplex_obj_zero_iff p _ hpl).1
      (a.app _ (boundary.lastVertex n)).2
    have hlast : H₁.app _ (boundary.lastVertex n) = fiberVertex p _ hpl := by
      apply yonedaEquiv.symm.injective
      refine pullback.hom_ext ?_ (stdSimplex.isTerminalObj₀.hom_ext _ _)
      rw [yonedaEquiv_symm_fiberVertex_fst, ← yonedaEquiv_symm_comp _ H₁,
        ← yonedaEquiv_symm_comp _ f₀, Category.assoc, hH₁def, pullback.lift_fst]
      have e : yonedaEquiv.symm (boundary.lastVertex n) ≫
          lift (stdSimplex.isTerminalObj₀.from _ ≫ stdSimplex.δ 0) (𝟙 _) =
          lift (stdSimplex.isTerminalObj₀.from _ ≫ stdSimplex.δ 0) (𝟙 _) ≫
            Δ[1] ◁ yonedaEquiv.symm (boundary.lastVertex n) := by
        rw [comp_lift, lift_whiskerLeft, ← Category.assoc, Category.comp_id, Category.id_comp,
          stdSimplex.isTerminalObj₀.hom_ext (_ ≫ _) (stdSimplex.isTerminalObj₀.from _)]
      rw [reassoc_of% e, hHl, ← Category.assoc, ← Category.assoc,
        stdSimplex.isTerminalObj₀.hom_ext (_ ≫ _) (𝟙 _), Category.id_comp]
    obtain ⟨v, hv⟩ := (isFinal_iff_extend_boundary _).1 hfin n H₁ hlast
    have hw : (Λ[1, 1] : (Δ[1] : SSet.{u}).Subcomplex).ι ▷ (∂Δ[n + 1] : SSet.{u}) ≫ H =
        (Λ[1, 1] : SSet.{u}) ◁ (∂Δ[n + 1]).ι ≫ snd _ _ ≫ v ≫ pullback.fst _ _ := by
      rw [whiskerLeft_snd_assoc, reassoc_of% hv, hH₁def, pullback.lift_fst, ← Category.assoc,
        ← horn_one_one_ι]
      congr 1
    set a' := (Subcomplex.unionProd.isPushout (Λ[1, 1] : (Δ[1] : SSet.{u}).Subcomplex)
      (∂Δ[n + 1])).desc H (snd _ _ ≫ v ≫ pullback.fst _ _) hw with ha'
    have sq' : CommSq a' (Λ[1, 1].unionProd ∂Δ[n + 1]).ι p (contractToLast (n + 1) ≫ g) := by
      refine ⟨(Subcomplex.unionProd.isPushout _ _).hom_ext ?_ ?_⟩
      · rw [ha', IsPushout.inl_desc_assoc, Subcomplex.unionProd.ι₁_ι_assoc, hHp]
      · rw [ha', IsPushout.inr_desc_assoc, Subcomplex.unionProd.ι₂_ι_assoc, Category.assoc,
          Category.assoc, pullback.condition, ← horn_one_one_ι,
          ← Category.id_comp ((_ ≫ stdSimplex.δ 0) ▷ _), ← lift_fst_snd, lift_whiskerRight,
          ← Category.assoc (fst _ _) (stdSimplex.isTerminalObj₀.from _),
          lift_δ_zero_contractToLast_assoc, hb₁]
        simp only [← Category.assoc]
        exact congrArg (· ≫ _) (stdSimplex.isTerminalObj₀.hom_ext _ _)
    have hcart : IsCartesianEdge p (prismLastEdge n ≫ a') := by
      have hx : prismLastEdge n ≫ a' =
          yonedaEquiv.symm (Edge.id (f₀.app _ (boundary.lastVertex n))).edge := by
        rw [prismLastEdge_eq, Category.assoc, ha', IsPushout.inl_desc,
          ← Category.comp_id (𝟙 Δ[1]),
          ← lift_whiskerLeft, Category.assoc, hHl, ← Category.assoc, ← Category.assoc,
          stdSimplex.isTerminalObj₀.hom_ext (_ ≫ _) (stdSimplex.isTerminalObj₀.from _),
          Category.assoc, yonedaEquiv_symm_comp, Edge.id_edge, ← stdSimplex.σ_comp_yonedaEquiv_symm,
          stdSimplex.isTerminalObj₀.hom_ext (stdSimplex.σ 0) (stdSimplex.isTerminalObj₀.from _)]
      rw [hx]
      exact isCartesianEdge_id p _
    have := hcart.hasLift_unionProd p n a' _ sq' rfl
    set ℓ := lift (stdSimplex.isTerminalObj₀.from _ ≫ stdSimplex.δ 1) (𝟙 _) ≫ sq'.lift
      with hℓ
    have hℓ₀ : (∂Δ[n + 1]).ι ≫ ℓ = f₀ := by
      have e : (∂Δ[n + 1]).ι ≫
          lift (stdSimplex.isTerminalObj₀.from _ ≫ stdSimplex.δ 1) (𝟙 _) =
          lift (stdSimplex.isTerminalObj₀.from _) (𝟙 _) ≫ stdSimplex.δ 1 ▷ _ ≫
            Subcomplex.unionProd.ι₁ _ _ ≫ (Λ[1, 1].unionProd ∂Δ[n + 1]).ι := by
        rw [Subcomplex.unionProd.ι₁_ι]
        exact CartesianMonoidalCategory.hom_ext _ _
          (by rw [Category.assoc, lift_fst, Category.assoc, Category.assoc, whiskerLeft_fst,
              whiskerRight_fst, lift_fst_assoc, ← Category.assoc]
              exact congrArg (· ≫ _) (stdSimplex.isTerminalObj₀.hom_ext _ _)) (by simp)
      rw [hℓ, reassoc_of% e, sq'.fac_left, ha', IsPushout.inl_desc, hH₀, lift_snd_assoc,
        Category.id_comp]
    have hℓp : ℓ ≫ p = g := by
      rw [hℓ, Category.assoc, sq'.fac_right, lift_δ_one_contractToLast_assoc,
        Category.id_comp]
    have hle : Subcomplex.range ℓ ≤ fiberwiseFinalSubcomplex p := by
      refine (range_le_fiberwiseFinalSubcomplex_iff p ℓ).2 fun i ↦ ?_
      let y : (∂Δ[n + 1] : SSet.{u}) _⦋0⦌ :=
        ⟨stdSimplex.obj₀Equiv.symm i, by rw [boundary_obj_eq_univ 0 (n + 1)]; trivial⟩
      have h : ℓ.app _ (stdSimplex.obj₀Equiv.symm i) = (a.app _ y).1 :=
        congrArg (fun φ ↦ φ.app _ y) hℓ₀
      rw [h]
      exact (a.app _ y).2
    refine ⟨⟨⟨Subcomplex.lift ℓ hle, ?_, ?_⟩⟩⟩
    · rw [← cancel_mono (fiberwiseFinalSubcomplex p).ι, Category.assoc, Subcomplex.lift_ι, hℓ₀]
    · rw [← cancel_mono (hasFinalFiberSubcomplex p).ι, Category.assoc, fiberwiseFinalRes_ι,
        Subcomplex.lift_ι_assoc, hℓp]

section Transfer

private lemma innerFibration_of_trivialFibration {P Q : SSet.{u}} {t : P ⟶ Q}
    (ht : modelCategoryQuillen.I.rlp t) : InnerFibration t := by
  rw [← rlp_monomorphisms] at ht
  exact ⟨antitone_rlp innerHornInclusions_le_monomorphisms _ ht⟩

variable {P Q B : SSet.{u}} (t : P ⟶ Q) (q : Q ⟶ B) [InnerFibration q]

private lemma mem_fiberwiseFinalSubcomplex_comp_iff (ht : modelCategoryQuillen.I.rlp t)
    (e : P _⦋0⦌) :
    e ∈ (fiberwiseFinalSubcomplex (t ≫ q)).obj (op ⦋0⦌) ↔
      t.app _ e ∈ (fiberwiseFinalSubcomplex q).obj (op ⦋0⦌) := by
  have := innerFibration_of_trivialFibration ht
  have : InnerFibration (t ≫ q) :=
    ⟨innerFibrations.comp_mem _ _ (mem_innerFibrations t) (mem_innerFibrations q)⟩
  have := quasicategory_of_innerFibration
    (pullback.snd (t ≫ q) (yonedaEquiv.symm ((t ≫ q).app _ e)))
  have := quasicategory_of_innerFibration
    (pullback.snd q (yonedaEquiv.symm ((t ≫ q).app _ e)))
  rw [mem_fiberwiseFinalSubcomplex_obj_zero_iff (t ≫ q) e rfl,
    mem_fiberwiseFinalSubcomplex_obj_zero_iff q (t.app _ e) (b := (t ≫ q).app _ e) rfl,
    ← isFinal_iff_of_trivialFibration (trivialFibration_fiberMap t rfl ht _),
    fiberMap_app_fiberVertex]

private lemma exists_comp_eq_of_trivialFibration {Y Z W : SSet.{u}} {f : Y ⟶ Z}
    (hf : modelCategoryQuillen.I.rlp f) (g : W ⟶ Z) : ∃ g' : W ⟶ Y, g' ≫ f = g := by
  rw [← rlp_monomorphisms] at hf
  have := hf (initial.to W) (monomorphisms.infer_property _)
  have sq : CommSq (initial.to Y) (initial.to W) f g := ⟨initial.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_right⟩

private lemma mem_hasFinalFiberSubcomplex_comp_iff (ht : modelCategoryQuillen.I.rlp t)
    (b : B _⦋0⦌) :
    b ∈ (hasFinalFiberSubcomplex (t ≫ q)).obj (op ⦋0⦌) ↔
      b ∈ (hasFinalFiberSubcomplex q).obj (op ⦋0⦌) := by
  have := innerFibration_of_trivialFibration ht
  have : InnerFibration (t ≫ q) :=
    ⟨innerFibrations.comp_mem _ _ (mem_innerFibrations t) (mem_innerFibrations q)⟩
  have := quasicategory_of_innerFibration (pullback.snd (t ≫ q) (yonedaEquiv.symm b))
  have := quasicategory_of_innerFibration (pullback.snd q (yonedaEquiv.symm b))
  have hφ := trivialFibration_fiberMap (q := q) t rfl ht b
  rw [mem_hasFinalFiberSubcomplex_obj_zero_iff, mem_hasFinalFiberSubcomplex_obj_zero_iff]
  refine ⟨fun ⟨ω, hω⟩ ↦ ⟨_, (isFinal_iff_of_trivialFibration hφ ω).2 hω⟩, fun ⟨ω, hω⟩ ↦ ?_⟩
  obtain ⟨ω', hω'⟩ := exists_comp_eq_of_trivialFibration hφ (yonedaEquiv.symm ω)
  refine ⟨yonedaEquiv ω', (isFinal_iff_of_trivialFibration hφ _).1 ?_⟩
  rwa [← yonedaEquiv_comp, hω', Equiv.apply_symm_apply]

theorem fiberwiseFinalSubcomplex_eq_preimage (ht : modelCategoryQuillen.I.rlp t) :
    fiberwiseFinalSubcomplex (t ≫ q) = (fiberwiseFinalSubcomplex q).preimage t := by
  refine subcomplex_ext_of_range fun m v ↦ ?_
  rw [range_le_fiberwiseFinalSubcomplex_iff, ← Subcomplex.image_le_iff, ← Subcomplex.range_comp,
    range_le_fiberwiseFinalSubcomplex_iff]
  exact forall_congr' fun i ↦ mem_fiberwiseFinalSubcomplex_comp_iff t q ht _

theorem hasFinalFiberSubcomplex_eq (ht : modelCategoryQuillen.I.rlp t) :
    hasFinalFiberSubcomplex (t ≫ q) = hasFinalFiberSubcomplex q := by
  refine subcomplex_ext_of_range fun m v ↦ ?_
  rw [range_le_hasFinalFiberSubcomplex_iff, range_le_hasFinalFiberSubcomplex_iff]
  exact forall_congr' fun i ↦ mem_hasFinalFiberSubcomplex_comp_iff t q ht _

private lemma hasLiftingProperty_fiberwiseFinalRes_iff {E B A A' : SSet.{u}} (p : E ⟶ B)
    (i : A ⟶ A') :
    HasLiftingProperty i (fiberwiseFinalRes p) ↔
      ∀ (a : A ⟶ E) (b : A' ⟶ B), Subcomplex.range a ≤ fiberwiseFinalSubcomplex p →
        Subcomplex.range b ≤ hasFinalFiberSubcomplex p → a ≫ p = i ≫ b →
          ∃ l : A' ⟶ E, Subcomplex.range l ≤ fiberwiseFinalSubcomplex p ∧ i ≫ l = a ∧
            l ≫ p = b := by
  have hι {Z : SSet.{u}} {S : E.Subcomplex} (f : Z ⟶ S) : Subcomplex.range (f ≫ S.ι) ≤ S := by
    rintro _ _ ⟨x, rfl⟩
    exact (f.app _ x).2
  have hι' {Z : SSet.{u}} {S : B.Subcomplex} (f : Z ⟶ S) : Subcomplex.range (f ≫ S.ι) ≤ S := by
    rintro _ _ ⟨x, rfl⟩
    exact (f.app _ x).2
  refine ⟨fun _ a b ha hb w ↦ ?_, fun h ↦ ⟨fun {a b} sq ↦ ?_⟩⟩
  · have sq : CommSq (Subcomplex.lift a ha) i (fiberwiseFinalRes p) (Subcomplex.lift b hb) :=
      ⟨by rw [← cancel_mono (hasFinalFiberSubcomplex p).ι, Category.assoc, fiberwiseFinalRes_ι,
        Subcomplex.lift_ι_assoc, w, Category.assoc, Subcomplex.lift_ι]⟩
    refine ⟨sq.lift ≫ (fiberwiseFinalSubcomplex p).ι, hι _, ?_, ?_⟩
    · rw [sq.fac_left_assoc, Subcomplex.lift_ι]
    · rw [Category.assoc, ← fiberwiseFinalRes_ι, sq.fac_right_assoc, Subcomplex.lift_ι]
  · obtain ⟨l, hl, hl₀, hl₁⟩ := h (a ≫ (fiberwiseFinalSubcomplex p).ι)
      (b ≫ (hasFinalFiberSubcomplex p).ι) (hι _) (hι' _)
      (by rw [Category.assoc, ← fiberwiseFinalRes_ι, sq.w_assoc])
    refine ⟨⟨⟨Subcomplex.lift l hl, ?_, ?_⟩⟩⟩
    · rw [← cancel_mono (fiberwiseFinalSubcomplex p).ι, Category.assoc, Subcomplex.lift_ι, hl₀]
    · rw [← cancel_mono (hasFinalFiberSubcomplex p).ι, Category.assoc, fiberwiseFinalRes_ι,
        Subcomplex.lift_ι_assoc, hl₁]

theorem trivialFibration_fiberwiseFinalRes_iff (ht : modelCategoryQuillen.I.rlp t) :
    modelCategoryQuillen.I.rlp (fiberwiseFinalRes (t ≫ q)) ↔
      modelCategoryQuillen.I.rlp (fiberwiseFinalRes q) := by
  have hrange {Z : SSet.{u}} (f : Z ⟶ P) :
      Subcomplex.range f ≤ fiberwiseFinalSubcomplex (t ≫ q) ↔
        Subcomplex.range (f ≫ t) ≤ fiberwiseFinalSubcomplex q := by
    rw [fiberwiseFinalSubcomplex_eq_preimage t q ht, ← Subcomplex.image_le_iff,
      ← Subcomplex.range_comp]
  have heq := hasFinalFiberSubcomplex_eq t q ht
  refine ⟨fun h _ _ _ ⟨n⟩ ↦ ?_, fun h _ _ _ ⟨n⟩ ↦ ?_⟩
  · have hn := h _ ⟨n⟩
    rw [hasLiftingProperty_fiberwiseFinalRes_iff] at hn ⊢
    intro a b ha hb w
    obtain ⟨a', rfl⟩ := exists_comp_eq_of_trivialFibration ht a
    obtain ⟨l, hl, hl₀, hl₁⟩ := hn a' b ((hrange a').2 ha) (by rwa [heq])
      (by rw [← Category.assoc, w])
    exact ⟨l ≫ t, (hrange l).1 hl, by rw [reassoc_of% hl₀], by rw [Category.assoc, hl₁]⟩
  · have hn := h _ ⟨n⟩
    rw [hasLiftingProperty_fiberwiseFinalRes_iff] at hn ⊢
    intro a b ha hb w
    obtain ⟨l, hl, hl₀, hl₁⟩ := hn (a ≫ t) b ((hrange a).1 ha) (by rwa [← heq])
      (by rw [Category.assoc, w])
    rw [← rlp_monomorphisms] at ht
    have := ht (∂Δ[n]).ι (monomorphisms.infer_property _)
    have sq : CommSq a (∂Δ[n]).ι t l := ⟨hl₀.symm⟩
    exact ⟨sq.lift, (hrange _).2 (by rw [sq.fac_right]; exact hl), sq.fac_left,
      by rw [← hl₁, ← sq.fac_right_assoc]⟩

end Transfer

namespace modelCategoryJoyal

theorem trivialFibration_pre_app {A A' : SSet.{u}} (j : A ⟶ A') [Mono j] [WeakEquivalence j]
    (X : SSet.{u}) [X.Quasicategory] : modelCategoryQuillen.I.rlp ((pre j).app X) := by
  rw [← rlp_monomorphisms]
  intro K L i (_ : Mono i)
  have : Fibration ((pre i).app X) := (fibration_iff_isofibration _).2
    (isofibration_pullbackObjObjπ (terminal.from X) i
      (Functor.PullbackObjObj.ofIsTerminal _ _ _ terminalIsTerminal))
  have : Cofibration j := (cofibration_iff j).2 (monomorphisms.infer_property j)
  exact (hasLiftingProperty_pullbackObjObjπ_comm j i (terminal.from X)
    (Functor.PullbackObjObj.ofIsTerminal _ _ _ terminalIsTerminal)
    (Functor.PullbackObjObj.ofIsTerminal _ _ _ terminalIsTerminal)).1
    (inferInstanceAs (HasLiftingProperty j ((pre i).app X)))

end modelCategoryJoyal

section Join

open modelCategoryJoyal

private structure ConeFactorization (K : SSet.{u}) where
  M : SSet.{u}
  j : fatJoin Δ[0] K ⟶ M
  π : M ⟶ join Δ[0] K
  s : join Δ[0] K ⟶ M
  mono_j : Mono j
  weakEquivalence_j : WeakEquivalence j
  mono_s : Mono s
  weakEquivalence_s : WeakEquivalence s
  fac : j ≫ π = fatJoinToJoin Δ[0] K
  s_π : s ≫ π = 𝟙 _
  joinInclRight_s : joinInclRight Δ[0] K ≫ s = fatJoinInclRight Δ[0] K ≫ j

private lemma nonempty_coneFactorization (K : SSet.{u}) : Nonempty (ConeFactorization K) := by
  let F := factorizationData (trivialCofibrations SSet.{u}) (fibrations SSet.{u})
    (fatJoinToJoin Δ[0] K)
  have hj : WeakEquivalence F.i := ⟨F.hi.2⟩
  have : Fibration F.p := ⟨F.hp⟩
  have := weakEquivalence_fatJoinToJoin Δ[0] K
  have : WeakEquivalence (F.i ≫ F.p) := by rw [F.fac]; infer_instance
  have : WeakEquivalence F.p := weakEquivalence_of_precomp F.i F.p
  have : Cofibration (joinInclRight Δ[0] K) :=
    (cofibration_iff _).2 (monomorphisms.infer_property _)
  have sq : CommSq (fatJoinInclRight Δ[0] K ≫ F.i) (joinInclRight Δ[0] K) F.p (𝟙 _) :=
    ⟨by rw [Category.assoc, F.fac, fatJoinInclRight_fatJoinToJoin, Category.comp_id]⟩
  have : WeakEquivalence (sq.lift ≫ F.p) := by rw [sq.fac_right]; infer_instance
  exact ⟨{ M := F.Z, j := F.i, π := F.p, s := sq.lift
           mono_j := (cofibration_iff F.i).1 ⟨F.hi.1⟩
           weakEquivalence_j := hj
           mono_s := mono_of_mono_fac sq.fac_right
           weakEquivalence_s := weakEquivalence_of_postcomp sq.lift F.p
           fac := F.fac
           s_π := sq.fac_right
           joinInclRight_s := sq.fac_left }⟩

theorem trivialFibration_fiberwiseFinalRes_join (K X : SSet.{u}) [X.Quasicategory] :
    modelCategoryQuillen.I.rlp
      (fiberwiseFinalRes ((MonoidalClosed.pre (joinInclRight (Δ[0] : SSet.{u}) K)).app X)) := by
  obtain ⟨F⟩ := nonempty_coneFactorization K
  have := F.mono_j
  have := F.weakEquivalence_j
  have := F.mono_s
  have := F.weakEquivalence_s
  have e : (pre F.j).app X ≫ (pre (fatJoinInclRight Δ[0] K)).app X =
      (pre F.s).app X ≫ (pre (joinInclRight Δ[0] K)).app X := by
    rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← pre_map, ← pre_map, F.joinInclRight_s]
  rw [← trivialFibration_fiberwiseFinalRes_iff _ _ (trivialFibration_pre_app F.s X), ← e,
    trivialFibration_fiberwiseFinalRes_iff _ _ (trivialFibration_pre_app F.j X)]
  exact trivialFibration_fiberwiseFinalRes_fatJoin K X

private lemma mem_fiberwiseFinalSubcomplex_join_iff_fatJoin {K X : SSet.{u}} [X.Quasicategory]
    (c : join Δ[0] K ⟶ X) :
    yonedaEquiv ((ihomPointEquiv _ X).symm c) ∈
        (fiberwiseFinalSubcomplex ((pre (joinInclRight (Δ[0] : SSet.{u}) K)).app X)).obj
          (op ⦋0⦌) ↔
      yonedaEquiv ((ihomPointEquiv _ X).symm (fatJoinToJoin Δ[0] K ≫ c)) ∈
        (fiberwiseFinalSubcomplex ((pre (fatJoinInclRight (Δ[0] : SSet.{u}) K)).app X)).obj
          (op ⦋0⦌) := by
  obtain ⟨F⟩ := nonempty_coneFactorization K
  have := F.mono_j
  have := F.weakEquivalence_j
  have := F.mono_s
  have := F.weakEquivalence_s
  have e : (pre F.j).app X ≫ (pre (fatJoinInclRight Δ[0] K)).app X =
      (pre F.s).app X ≫ (pre (joinInclRight Δ[0] K)).app X := by
    rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← pre_map, ← pre_map, F.joinInclRight_s]
  have key {A : SSet.{u}} (i : A ⟶ F.M) [Mono i] [WeakEquivalence i] {B : SSet.{u}}
      (q : (ihom A).obj X ⟶ B) [InnerFibration q] :
      yonedaEquiv ((ihomPointEquiv F.M X).symm (F.π ≫ c)) ∈
          (fiberwiseFinalSubcomplex ((pre i).app X ≫ q)).obj (op ⦋0⦌) ↔
        yonedaEquiv ((ihomPointEquiv A X).symm (i ≫ F.π ≫ c)) ∈
          (fiberwiseFinalSubcomplex q).obj (op ⦋0⦌) := by
    rw [fiberwiseFinalSubcomplex_eq_preimage _ _ (trivialFibration_pre_app i X),
      ← pre_app_app_yonedaEquiv]
    exact Iff.rfl
  have hs := key F.s ((pre (joinInclRight Δ[0] K)).app X)
  have hj := key F.j ((pre (fatJoinInclRight Δ[0] K)).app X)
  rw [← Category.assoc, F.s_π, Category.id_comp] at hs
  rw [← Category.assoc, F.fac] at hj
  rw [← hs, ← hj, e]

theorem mem_fiberwiseFinalSubcomplex_join_iff {K X : SSet.{u}} [X.Quasicategory]
    (c : join Δ[0] K ⟶ X) :
    yonedaEquiv ((ihomPointEquiv _ X).symm c) ∈
        (fiberwiseFinalSubcomplex
          ((MonoidalClosed.pre (joinInclRight (Δ[0] : SSet.{u}) K)).app X)).obj (op ⦋0⦌) ↔
      IsFinal ((sliceObjEquiv K (Under.mk (joinInclRight Δ[0] K ≫ c)) 0).symm ⟨c, rfl⟩) := by
  have hφ : fatJoinInclRight Δ[0] K ≫ fatJoinToJoin Δ[0] K ≫ c = joinInclRight Δ[0] K ≫ c :=
    fatJoinInclRight_fatJoinToJoin_assoc _ _ _
  have hb : ihomPointEquiv K X (yonedaEquiv.symm
      (yonedaEquiv ((ihomPointEquiv K X).symm (joinInclRight Δ[0] K ≫ c)))) =
        joinInclRight Δ[0] K ≫ c := by
    rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  have h := (pre_app_app_yonedaEquiv (fatJoinInclRight Δ[0] K) _).trans
    (congrArg (fun g ↦ yonedaEquiv ((ihomPointEquiv K X).symm g)) hφ)
  have hv : (fatConeFiberIso _ hb).hom.app _ (fiberVertex _ _ h) =
      ((sliceToFatSlice K).app _).app _ (yonedaEquiv (joinAdjunct c)) := by
    rw [fatConeFiberIso_hom_app_fiberVertex _ hb _ hφ, ← yonedaEquiv_comp]
    exact congrArg yonedaEquiv (joinAdjunct_sliceToFatSlice_app c).symm
  rw [mem_fiberwiseFinalSubcomplex_join_iff_fatJoin,
    mem_fiberwiseFinalSubcomplex_obj_zero_iff _ _ h,
    ← isFinal_iso_hom_app_iff (fatConeFiberIso _ hb), hv,
    ← isFinal_iso_hom_app_iff (commaConeIsoFatSlice (joinInclRight Δ[0] K ≫ c)).symm,
    Iso.symm_hom, ← yonedaEquiv_comp, ← yonedaEquiv_comp, Category.assoc, ← sliceToCommaCone,
    yonedaEquiv_comp, ← yonedaEquiv_joinAdjunct]
  exact (isFinal_iff_isLimitCone_sliceToCommaCone _ _).symm

theorem mem_hasFinalFiberSubcomplex_join_iff {K X : SSet.{u}} [X.Quasicategory] (d : K ⟶ X) :
    yonedaEquiv ((ihomPointEquiv K X).symm d) ∈
        (hasFinalFiberSubcomplex
          ((MonoidalClosed.pre (joinInclRight (Δ[0] : SSet.{u}) K)).app X)).obj (op ⦋0⦌) ↔
      ∃ w : ((slice K).obj (Under.mk d)) _⦋0⦌, IsFinal w := by
  rw [mem_hasFinalFiberSubcomplex_obj_zero_iff]
  constructor
  · rintro ⟨ω, hω⟩
    obtain ⟨e, h, rfl⟩ := exists_fiberVertex_eq _ ω
    have he := (mem_fiberwiseFinalSubcomplex_obj_zero_iff _ e h).2 hω
    obtain ⟨c, rfl⟩ : ∃ c, e = yonedaEquiv ((ihomPointEquiv _ X).symm c) :=
      ⟨_, by rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply]⟩
    have hc : joinInclRight Δ[0] K ≫ c = d := by
      rw [pre_app_app_yonedaEquiv] at h
      exact (ihomPointEquiv K X).symm.injective (yonedaEquiv.injective h)
    subst hc
    exact ⟨_, (mem_fiberwiseFinalSubcomplex_join_iff c).1 he⟩
  · rintro ⟨w, hw⟩
    obtain ⟨c, hc, rfl⟩ : ∃ (c : join Δ[0] K ⟶ X) (hc : joinInclRight Δ[0] K ≫ c = d),
        w = (sliceObjEquiv K (Under.mk d) 0).symm ⟨c, hc⟩ :=
      ⟨_, (sliceObjEquiv K _ 0 w).2, ((sliceObjEquiv K _ 0).symm_apply_apply w).symm⟩
    subst hc
    have h := pre_app_app_yonedaEquiv (X := X) (joinInclRight Δ[0] K) c
    exact ⟨fiberVertex _ _ h, (mem_fiberwiseFinalSubcomplex_obj_zero_iff _ _ h).1
      ((mem_fiberwiseFinalSubcomplex_join_iff c).2 hw)⟩

end Join

end SSet
