import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.FunctionSpace
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.RightPushoutProduct

open CategoryTheory Limits Simplicial HomotopicalAlgebra MorphismProperty Opposite
  MonoidalCategory CartesianMonoidalCategory

universe u

namespace SSet

section BoundaryOne

theorem boundary_one_apply {n : SimplexCategoryᵒᵖ} (x : (∂Δ[1] : SSet.{u}).obj n)
    (i : Fin (n.unop.len + 1)) : stdSimplex.asOrderHom x.1 i = stdSimplex.asOrderHom x.1 0 := by
  obtain ⟨n⟩ := n
  induction n using SimplexCategory.rec with | _ n => ?_
  obtain ⟨j, hj⟩ := (mem_boundary_iff_notMem_range x.1).1 x.2
  have h₁ : x.1 i ≠ j := fun h ↦ hj ⟨i, h⟩
  have h₂ : x.1 0 ≠ j := fun h ↦ hj ⟨0, h⟩
  refine Fin.ext ?_
  have := Fin.val_ne_iff.2 h₁
  have := Fin.val_ne_iff.2 h₂
  have := (x.1 i).isLt
  have := (x.1 0).isLt
  have := j.isLt
  change (x.1 i : ℕ) = x.1 0
  omega

noncomputable def boundaryOneDesc {E F : SSet.{u}} (f₀ f₁ : E ⟶ F) :
    E ⊗ (∂Δ[1] : SSet.{u}) ⟶ F where
  app n := TypeCat.ofHom fun z ↦
    if stdSimplex.asOrderHom z.2.1 0 = 0 then f₀.app n z.1 else f₁.app n z.1
  naturality n m θ := by
    ext z
    have h : stdSimplex.asOrderHom ((∂Δ[1] : SSet.{u}).map θ z.2).1 0 =
        stdSimplex.asOrderHom z.2.1 0 :=
      boundary_one_apply z.2 _
    change (if stdSimplex.asOrderHom ((∂Δ[1] : SSet.{u}).map θ z.2).1 0 = 0 then
      f₀.app m (E.map θ z.1) else f₁.app m (E.map θ z.1)) =
      F.map θ (if stdSimplex.asOrderHom z.2.1 0 = 0 then f₀.app n z.1 else f₁.app n z.1)
    rw [h]
    split_ifs
    · exact NatTrans.naturality_apply f₀ θ z.1
    · exact NatTrans.naturality_apply f₁ θ z.1

theorem boundaryOneDesc_app {E F : SSet.{u}} (f₀ f₁ : E ⟶ F) (n : SimplexCategoryᵒᵖ)
    (z : (E ⊗ (∂Δ[1] : SSet.{u})).obj n) :
    (boundaryOneDesc f₀ f₁).app n z =
      if stdSimplex.asOrderHom z.2.1 0 = 0 then f₀.app n z.1 else f₁.app n z.1 :=
  rfl

theorem boundaryOneDesc_self {E F : SSet.{u}} (f : E ⟶ F) :
    boundaryOneDesc f f = fst E (∂Δ[1] : SSet.{u}) ≫ f := by
  ext n z
  change (if _ then _ else _) = _
  split_ifs <;> rfl

@[reassoc]
theorem boundaryOneDesc_comp {E F G : SSet.{u}} (f₀ f₁ : E ⟶ F) (g : F ⟶ G) :
    boundaryOneDesc f₀ f₁ ≫ g = boundaryOneDesc (f₀ ≫ g) (f₁ ≫ g) := by
  ext n z
  change g.app n (if _ then _ else _) = (if _ then _ else _)
  split_ifs <;> rfl

@[reassoc]
theorem whiskerRight_boundaryOneDesc {E E' F : SSet.{u}} (f : E' ⟶ E) (f₀ f₁ : E ⟶ F) :
    f ▷ _ ≫ boundaryOneDesc f₀ f₁ = boundaryOneDesc (f ≫ f₀) (f ≫ f₁) := by
  ext n z
  change (if _ then _ else _) = (if _ then _ else _)
  rfl

theorem mem_boundary_one_of_forall {n : SimplexCategoryᵒᵖ} (x : (Δ[1] : SSet.{u}).obj n)
    (i : Fin 2) (h : ∀ k, stdSimplex.asOrderHom x k = i) :
    x ∈ (∂Δ[1] : (Δ[1] : SSet.{u}).Subcomplex).obj n := by
  obtain ⟨n⟩ := n
  induction n using SimplexCategory.rec with | _ n => ?_
  refine (mem_boundary_iff_notMem_range x).2 ⟨i.rev, ?_⟩
  rintro ⟨k, hk⟩
  have hi : i = i.rev := (h k).symm.trans hk
  fin_cases i <;> exact absurd hi (by decide)

theorem ι_comp_of_boundaryOneDesc {E F : SSet.{u}} {H : E ⊗ Δ[1] ⟶ F} {f₀ f₁ : E ⟶ F}
    (h : E ◁ (∂Δ[1]).ι ≫ H = boundaryOneDesc f₀ f₁) : ι₀ ≫ H = f₀ ∧ ι₁ ≫ H = f₁ := by
  have hl (n : SimplexCategoryᵒᵖ) (z : (E ⊗ (∂Δ[1] : SSet.{u})).obj n) :
      H.app n ((E ◁ (∂Δ[1]).ι).app n z) = (boundaryOneDesc f₀ f₁).app n z :=
    ConcreteCategory.congr_hom (congr_app h n) z
  refine ⟨?_, ?_⟩
  · ext ⟨n⟩ e
    induction n using SimplexCategory.rec with | _ n => ?_
    refine (hl _ (e, ⟨_, mem_boundary_one_of_forall _ 0 fun k ↦ ι₀_app_snd_apply e k⟩)).trans ?_
    exact (boundaryOneDesc_app _ _ _ _).trans ((if_pos (ι₀_app_snd_apply e 0)).trans rfl)
  · ext ⟨n⟩ e
    induction n using SimplexCategory.rec with | _ n => ?_
    refine (hl _ (e, ⟨_, mem_boundary_one_of_forall _ 1 fun k ↦ ι₁_app_snd_apply e k⟩)).trans ?_
    exact (boundaryOneDesc_app _ _ _ _).trans
      ((if_neg fun h ↦ absurd ((ι₁_app_snd_apply e 0).symm.trans h) (by decide)).trans rfl)

theorem whiskerLeft_horn_comp {E F : SSet.{u}} {H : E ⊗ Δ[1] ⟶ F} {g : E ⟶ F}
    (h : ι₁ ≫ H = g) : E ◁ Λ[1, 1].ι ≫ H = fst _ _ ≫ g := by
  ext ⟨n⟩ z
  induction n using SimplexCategory.rec with | _ n => ?_
  obtain ⟨e, x⟩ := z
  have hx : x.1 = (ι₁.app _ e).2 := by
    obtain ⟨j, hj⟩ := (Set.ne_univ_iff_exists_notMem _).1 ((mem_horn_iff _ x.1).1 x.2)
    simp only [Set.union_singleton, Set.mem_insert_iff, Set.mem_range, not_or, not_exists] at hj
    refine stdSimplex.ext _ _ fun k ↦ (?_ : _ = (1 : Fin 2)).trans (ι₁_app_snd_apply e k).symm
    have key : ∀ c j : Fin 2, j ≠ 1 → c ≠ j → c = 1 := by decide
    exact key _ _ hj.1 (hj.2 k)
  have h' : H.app _ (ι₁.app _ e) = g.app _ e := ConcreteCategory.congr_hom (congr_app h _) e
  refine Eq.trans ?_ h'
  exact congrArg (H.app _) (Prod.ext rfl hx : ((e, x.1) : (E ⊗ Δ[1]).obj _) = ι₁.app _ e)

end BoundaryOne

private def contraction (n : ℕ) : (Δ[1] ⊗ Δ[n] : SSet.{u}) ⟶ Δ[n] where
  app _ := ↾fun z ↦ stdSimplex.objMk
    ⟨fun i ↦ if (stdSimplex.objEquiv z.1).toOrderHom i = 0 then 0
      else (stdSimplex.objEquiv z.2).toOrderHom i, fun i j hij ↦ by
      have h₁ := (stdSimplex.objEquiv z.1).toOrderHom.monotone hij
      have h₂ := (stdSimplex.objEquiv z.2).toOrderHom.monotone hij
      dsimp only
      by_cases hi : (stdSimplex.objEquiv z.1).toOrderHom i = 0
      · rw [if_pos hi]
        exact Fin.zero_le _
      · have hj : (stdSimplex.objEquiv z.1).toOrderHom j ≠ 0 := fun hj ↦
          hi (le_antisymm (hj ▸ h₁) (Fin.zero_le _))
        rw [if_neg hi, if_neg hj]
        exact h₂⟩
  naturality _ _ _ := rfl

private abbrev incl (ε : Fin 2) (K : SSet.{u}) : K ⟶ Δ[1] ⊗ K :=
  lift (const (stdSimplex.obj₀Equiv.symm ε)) (𝟙 K)

private lemma incl_whiskerLeft (ε : Fin 2) {K L : SSet.{u}} (f : K ⟶ L) :
    incl ε K ≫ (Δ[1] : SSet.{u}) ◁ f = f ≫ incl ε L :=
  CartesianMonoidalCategory.hom_ext _ _ rfl rfl

private lemma incl_contraction (ε : Fin 2) (n : ℕ) :
    incl ε Δ[n] ≫ contraction.{u} n =
      if ε = 0 then const (stdSimplex.obj₀Equiv.symm 0) else 𝟙 _ := by
  ext ⟨k⟩ z
  induction k using SimplexCategory.rec with | _ k => ?_
  refine stdSimplex.ext _ _ fun i ↦ ?_
  fin_cases ε <;> rfl

private def hornVertex (ε : Fin 2) : (Λ[1, ε] : SSet.{u}) _⦋0⦌ :=
  ⟨stdSimplex.obj₀Equiv.symm ε, by
    rw [mem_horn_iff_notMem_range]
    refine ⟨ε.rev, by fin_cases ε <;> decide, ?_⟩
    rintro ⟨i, hi⟩
    exact (by fin_cases ε <;> decide : ε.rev ≠ ε) (hi.symm.trans (by fin_cases i; rfl))⟩

private lemma horn_one_ι (ε : Fin 2) :
    Λ[1, ε].ι = const.{u} (stdSimplex.obj₀Equiv.symm ε) := by
  ext ⟨k⟩ x
  induction k using SimplexCategory.rec with | _ k => ?_
  refine stdSimplex.ext _ _ fun i ↦ ?_
  obtain ⟨j, hj, hji⟩ := (mem_horn_iff_notMem_range _ _).1 x.2
  have key : ∀ c j ε : Fin 2, j ≠ ε → c ≠ j → c = ε := by decide
  exact key _ j ε hj fun h ↦ hji ⟨i, h⟩

private lemma horn_one_ι_whiskerRight (ε : Fin 2) (K : SSet.{u}) :
    Λ[1, ε].ι ▷ K = snd _ _ ≫ incl ε K :=
  CartesianMonoidalCategory.hom_ext _ _ (by rw [whiskerRight_fst, horn_one_ι]; rfl) rfl

private lemma incl_eq (ε : Fin 2) (K : SSet.{u}) :
    incl ε K = lift (const (hornVertex ε)) (𝟙 K) ≫ Λ[1, ε].ι ▷ K :=
  CartesianMonoidalCategory.hom_ext _ _ rfl rfl

private lemma exists_extension_of_fiber {E B : SSet.{u}} {p : E ⟶ B} (b₀ : B _⦋0⦌)
    (h : modelCategoryQuillen.I.rlp (pullback.snd p (yonedaEquiv.symm b₀))) (m : ℕ)
    (c : (∂Δ[m] : SSet.{u}) ⟶ E) (hc : c ≫ p = const b₀) :
    ∃ e : Δ[m] ⟶ E, (∂Δ[m]).ι ≫ e = c ∧ e ≫ p = const b₀ := by
  have hb (K : SSet.{u}) : stdSimplex.isTerminalObj₀.from K ≫ yonedaEquiv.symm b₀ = const b₀ := by
    rw [yonedaEquiv_symm_zero, comp_const]
  have sq : CommSq (pullback.lift c (stdSimplex.isTerminalObj₀.from _) (hc.trans (hb _).symm))
      (∂Δ[m]).ι (pullback.snd p (yonedaEquiv.symm b₀)) (stdSimplex.isTerminalObj₀.from _) :=
    ⟨stdSimplex.isTerminalObj₀.hom_ext _ _⟩
  obtain ⟨l⟩ := ((h _ ⟨m⟩).sq_hasLift sq).exists_lift
  refine ⟨l.l ≫ pullback.fst _ _, ?_, ?_⟩
  · rw [← Category.assoc, l.fac_left, pullback.lift_fst]
  · rw [Category.assoc, pullback.condition, ← Category.assoc, l.fac_right, hb]

theorem trivialFibration_of_rightFibrations_of_fiber {E B : SSet.{u}} {p : E ⟶ B}
    (hp : rightFibrations p)
    (h : ∀ b : B _⦋0⦌, modelCategoryQuillen.I.rlp (pullback.snd p (yonedaEquiv.symm b))) :
    modelCategoryQuillen.I.rlp p := by
  rintro _ _ _ ⟨k⟩
  refine ⟨fun {a b} sq ↦ ?_⟩
  cases k with
  | zero =>
    have hb : b = const (yonedaEquiv b) :=
      (yonedaEquiv.symm_apply_apply b).symm.trans (yonedaEquiv_symm_zero _)
    obtain ⟨e, he, hep⟩ := exists_extension_of_fiber _ (h (yonedaEquiv b)) 0 a
      (sq.w.trans ((congrArg (_ ≫ ·) hb).trans (comp_const _ _)))
    exact ⟨⟨⟨e, he, hep.trans hb.symm⟩⟩⟩
  | succ n =>
  let q := pullback.snd p b
  have hq : rightFibrations q := MorphismProperty.pullback_snd (P := rightHornInclusions.rlp) _ _ hp
  have : InnerFibration q := innerFibration_of_rightFibrations hq
  have : InnerFibration (stdSimplex.isoNerve.{u} (n + 1)).hom := ⟨fun _ _ _ _ ↦ inferInstance⟩
  have : (Δ[n + 1] : SSet.{u}).Quasicategory :=
    quasicategory_of_innerFibration (stdSimplex.isoNerve.{u} (n + 1)).hom
  have : (pullback p b).Quasicategory := quasicategory_of_innerFibration q
  let a' : (∂Δ[n + 1] : SSet.{u}) ⟶ pullback p b := pullback.lift a (∂Δ[n + 1]).ι sq.w
  let g := contraction.{u} (n + 1)
  have hg (ε : Fin 2) : Λ[1, ε].ι ▷ Δ[n + 1] ≫ g =
      snd _ _ ≫ if ε = 0 then const (stdSimplex.obj₀Equiv.symm 0) else 𝟙 _ := by
    rw [horn_one_ι_whiskerRight, Category.assoc, incl_contraction]
  let sq₁ := Functor.PushoutObjObj.ofIsInitialRight (curriedTensor SSet.{u}) Λ[1, 1].ι
    (Subcomplex.homOfLE (bot_le : ⊥ ≤ ∂Δ[n + 1])) Subcomplex.isInitialBot
  have h₁ : HasLiftingProperty (Λ[1, 1].ι ▷ (∂Δ[n + 1] : SSet.{u})) q :=
    rightAnodyneExtensions_pushoutObjObjι_left sq₁
      (rightAnodyneExtensions.horn_ι (by decide : (0 : Fin 2) < 1)) q hq
  obtain ⟨⟨H, hHl, hHr⟩⟩ := (h₁.sq_hasLift (⟨by
      rw [Category.assoc, pullback.lift_snd, ← whisker_exchange_assoc, hg, if_neg (by decide),
        Category.comp_id]
      exact (whiskerLeft_snd _ _).symm⟩ :
    CommSq (snd _ _ ≫ a') (Λ[1, 1].ι ▷ _) q ((Δ[1] : SSet.{u}) ◁ (∂Δ[n + 1]).ι ≫ g))).exists_lift
  let v₀ : (Δ[n + 1] : SSet.{u}) _⦋0⦌ := stdSimplex.obj₀Equiv.symm 0
  have hH₀ : incl 0 _ ≫ H ≫ q = (∂Δ[n + 1]).ι ≫ const v₀ := by
    rw [hHr, reassoc_of% incl_whiskerLeft, incl_contraction]
    rfl
  obtain ⟨e, he, hep⟩ := exists_extension_of_fiber (b.app _ v₀) (h _) (n + 1)
    (incl 0 _ ≫ H ≫ pullback.fst _ _) (by
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc,
        ← Category.assoc, Category.assoc (incl 0 _), hH₀, Category.assoc, const_comp,
        comp_const])
  let e' : (Δ[n + 1] : SSet.{u}) ⟶ pullback p b := pullback.lift e (const v₀) (by
    rw [hep, const_comp])
  let sq₂ :=
    Subcomplex.unionProd.pushoutObjObj Λ[1, 0] (∂Δ[n + 1] : (Δ[n + 1] : SSet.{u}).Subcomplex)
  have hcompat : incl 0 _ ≫ H = (∂Δ[n + 1]).ι ≫ e' := pullback.hom_ext
    (by rw [Category.assoc, ← he, Category.assoc, pullback.lift_fst])
    (by rw [Category.assoc (∂Δ[n + 1]).ι, pullback.lift_snd, Category.assoc (incl 0 _)]
        exact hH₀)
  have hw : Λ[1, 0].ι ▷ (∂Δ[n + 1] : SSet.{u}) ≫ H =
      (Λ[1, 0] : SSet.{u}) ◁ (∂Δ[n + 1]).ι ≫ snd _ _ ≫ e' := by
    rw [horn_one_ι_whiskerRight, Category.assoc, hcompat, whiskerLeft_snd_assoc]
  let u := sq₂.isPushout.desc H (snd _ _ ≫ e') hw
  have hu : CommSq u (Subcomplex.unionProd Λ[1, 0] ∂Δ[n + 1]).ι q g := ⟨by
    refine sq₂.isPushout.hom_ext ?_ ?_
    · rw [sq₂.isPushout.inl_desc_assoc, hHr]
      rfl
    · rw [sq₂.isPushout.inr_desc_assoc, Category.assoc, pullback.lift_snd]
      exact ((congrArg (snd _ _ ≫ ·) rfl).trans (hg 0).symm)⟩
  have hinv (z : (Subcomplex.unionProd Λ[1, 0] ∂Δ[n + 1] : SSet.{u}) _⦋1⦌)
      (h₀ : z.1.1 0 = 0) (h₁ : z.1.1 1 = 1) (h₂ : z.1.2 0 = 0) (h₃ : z.1.2 1 = 0) :
      Nonempty (Edge.mk' (u.app _ z)).InvStruct := by
    refine nonempty_invStruct_of_rightFibrations hq _
      ⟨(Edge.InvStruct.invStructId v₀).ofEq ?_⟩
    refine (?_ : _ = g.app _ z.1).trans (ConcreteCategory.congr_hom (congr_app hu.w _) z).symm
    refine stdSimplex.ext _ _ fun i ↦ ?_
    fin_cases i
    · exact (if_pos h₀).symm
    · exact ((if_neg fun h ↦ absurd (h₁.symm.trans h) (by decide)).trans h₃).symm
  obtain ⟨⟨L, hLl, hLr⟩⟩ := (hasLift_unionProd_horn_one_zero q hu hinv).exists_lift
  have hL₁ : incl 1 _ ≫ L ≫ q = 𝟙 _ := by
    rw [hLr, incl_contraction]
    rfl
  refine ⟨⟨⟨incl 1 _ ≫ L ≫ pullback.fst _ _, ?_, ?_⟩⟩⟩
  · have hl : (Δ[1] : SSet.{u}) ◁ (∂Δ[n + 1]).ι ≫ L = H :=
      (sq₂.inl_ι_assoc _).symm.trans ((congrArg (sq₂.inl ≫ ·) hLl).trans
        (sq₂.isPushout.inl_desc _ _ _))
    rw [← Category.assoc, ← Category.assoc, ← incl_whiskerLeft, Category.assoc (incl 1 _), hl,
      incl_eq, Category.assoc (lift _ _), hHl]
    simp only [lift_snd_assoc, Category.id_comp]
    exact pullback.lift_fst _ _ _
  · rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc L,
      ← Category.assoc, hL₁, Category.id_comp]

end SSet
