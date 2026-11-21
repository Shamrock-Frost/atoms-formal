import Atoms.ForMathlib.CategoryTheory.Monoidal.DayConvolution.JoinSlice
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj

open CategoryTheory Limits

universe w u

namespace CategoryTheory.WithInitial

section Leibniz

variable {𝒞 : Type*} [Category* 𝒞] (F : 𝒞 ⥤ 𝒞 ⥤ 𝒞) (incl : ∀ X B : 𝒞, B ⟶ (F.obj X).obj B)
  (hincl : ∀ {X Y : 𝒞} (f : X ⟶ Y) (B : 𝒞), incl X B ≫ (F.map f).app B = incl Y B)

private def underFunctor (B : 𝒞) : 𝒞 ⥤ Under B where
  obj X := Under.mk (incl X B)
  map f := Under.homMk ((F.map f).app B) (hincl f B)
  map_id X := by
    ext1
    simp
  map_comp f g := by
    ext1
    simp

private structure UnderAdjoints where
  incl_comp_map (X : 𝒞) {B B' : 𝒞} (g : B' ⟶ B) :
    incl X B' ≫ (F.obj X).map g = g ≫ incl X B
  R (B : 𝒞) : Under B ⥤ 𝒞
  adj (B : 𝒞) : underFunctor F incl hincl B ⊣ R B

variable {F incl hincl} (D : UnderAdjoints F incl hincl)

namespace UnderAdjoints

private def transpose {B X : 𝒞} {t : Under B} (ψ : X ⟶ (D.R B).obj t) :
    (F.obj X).obj B ⟶ t.right :=
  (((D.adj B).homEquiv _ _).symm ψ).right

private lemma incl_comp_transpose {B X : 𝒞} {t : Under B} (ψ : X ⟶ (D.R B).obj t) :
    incl X B ≫ D.transpose ψ = t.hom :=
  Under.w (((D.adj B).homEquiv _ _).symm ψ)

private def untranspose {B X : 𝒞} {t : Under B} (φ : (F.obj X).obj B ⟶ t.right)
    (h : incl X B ≫ φ = t.hom) : X ⟶ (D.R B).obj t :=
  (D.adj B).homEquiv _ _ (Under.homMk φ h)

private lemma transpose_untranspose {B X : 𝒞} {t : Under B}
    (φ : (F.obj X).obj B ⟶ t.right) (h : incl X B ≫ φ = t.hom) :
    D.transpose (D.untranspose φ h) = φ := by
  rw [transpose, untranspose, Equiv.symm_apply_apply]
  rfl

private lemma transpose_injective {B X : 𝒞} {t : Under B} {ψ ψ' : X ⟶ (D.R B).obj t}
    (h : D.transpose ψ = D.transpose ψ') : ψ = ψ' :=
  ((D.adj B).homEquiv _ _).symm.injective (Under.UnderMorphism.ext h)

private lemma transpose_comp {B X X' : 𝒞} {t : Under B} (f : X' ⟶ X)
    (ψ : X ⟶ (D.R B).obj t) : D.transpose (f ≫ ψ) = (F.map f).app B ≫ D.transpose ψ := by
  rw [transpose, Adjunction.homEquiv_naturality_left_symm, Under.comp_right]
  rfl

private lemma transpose_comp_map {B X : 𝒞} {t t' : Under B} (ψ : X ⟶ (D.R B).obj t)
    (k : t ⟶ t') : D.transpose (ψ ≫ (D.R B).map k) = D.transpose ψ ≫ k.right := by
  rw [transpose, Adjunction.homEquiv_naturality_right_symm, Under.comp_right]
  rfl

private lemma transpose_comp_map_homMk {B X : 𝒞} {t t' : Under B} (ψ : X ⟶ (D.R B).obj t)
    (k : t.right ⟶ t'.right) (hk : t.hom ≫ k = t'.hom) :
    D.transpose (ψ ≫ (D.R B).map (Under.homMk k hk)) = D.transpose ψ ≫ k :=
  D.transpose_comp_map ψ _

private def res {B B' : 𝒞} (g : B' ⟶ B) (t : Under B) :
    (D.R B).obj t ⟶ (D.R B').obj (Under.mk (g ≫ t.hom)) :=
  D.untranspose ((F.obj _).map g ≫ D.transpose (𝟙 _)) (by
    rw [← Category.assoc, D.incl_comp_map, Category.assoc, incl_comp_transpose]
    rfl)

private lemma transpose_comp_res {B B' X : 𝒞} (g : B' ⟶ B) {t : Under B}
    (ψ : X ⟶ (D.R B).obj t) :
    D.transpose (ψ ≫ D.res g t) = (F.obj X).map g ≫ D.transpose ψ := by
  rw [transpose_comp, res, transpose_untranspose, ← Category.assoc, ← NatTrans.naturality,
    Category.assoc, ← transpose_comp, Category.comp_id]

private lemma transpose_res {B B' : 𝒞} (g : B' ⟶ B) (t : Under B) :
    D.transpose (D.res g t) = (F.obj _).map g ≫ D.transpose (𝟙 ((D.R B).obj t)) :=
  D.transpose_untranspose _ _

private lemma res_comp_map {B B' : 𝒞} (g : B' ⟶ B) {t t' : Under B} (k : t ⟶ t') :
    D.res g t ≫ (D.R B').map (Under.homMk k.right (by simp [Under.w k]) :
      Under.mk (g ≫ t.hom) ⟶ Under.mk (g ≫ t'.hom)) = (D.R B).map k ≫ D.res g t' := by
  apply D.transpose_injective
  rw [transpose_comp_map, transpose_comp_res, ← Category.id_comp ((D.R B).map k),
    transpose_comp_map, res, transpose_untranspose, Category.assoc]
  rfl

private lemma res_comp {A B T : 𝒞} (a : A ⟶ B) (b : B ⟶ T) (t : Under T) :
    D.res b t ≫ D.res a (Under.mk (b ≫ t.hom)) = D.res (a ≫ b) t ≫
      (D.R A).map (Under.homMk (𝟙 _) (by simp) :
        Under.mk ((a ≫ b) ≫ t.hom) ⟶ Under.mk (a ≫ b ≫ t.hom)) := by
  apply D.transpose_injective
  rw [transpose_comp_res, transpose_comp_map_homMk, Category.comp_id,
    ← Category.id_comp (D.res b t), ← Category.id_comp (D.res (a ≫ b) t), transpose_comp_res,
    transpose_comp_res, Functor.map_comp, Category.assoc]

private lemma res_id {B : 𝒞} (t : Under B) :
    D.res (𝟙 B) t = (D.R B).map (Under.homMk (𝟙 _) (by simp) : t ⟶ Under.mk (𝟙 B ≫ t.hom)) := by
  apply D.transpose_injective
  refine (congrArg D.transpose (Category.id_comp (D.res (𝟙 B) t)).symm).trans
    ((D.transpose_comp_res (𝟙 B) (𝟙 _)).trans ?_)
  refine ((congrArg (· ≫ D.transpose (𝟙 _)) (Functor.map_id _ _)).trans
    ((Category.id_comp _).trans (Category.comp_id _).symm)).trans ?_
  exact (D.transpose_comp_map_homMk (t := t) (t' := Under.mk (𝟙 B ≫ t.hom)) (𝟙 _) (𝟙 _)
    (by simp)).symm.trans (congrArg D.transpose (Category.id_comp _))

variable [Limits.HasPullbacks 𝒞] {X₂ Y₂ E S : 𝒞} (f₂ : X₂ ⟶ Y₂) (p : E ⟶ S) (e : Y₂ ⟶ E)

private noncomputable def leibnizSlice :
    (D.R Y₂).obj (Under.mk e) ⟶ pullback ((D.R X₂).map (Under.homMk p (by simp) :
      Under.mk (f₂ ≫ e) ⟶ Under.mk (f₂ ≫ e ≫ p))) (D.res f₂ (Under.mk (e ≫ p))) :=
  pullback.lift (D.res f₂ (Under.mk e))
    ((D.R Y₂).map (Under.homMk p : Under.mk e ⟶ Under.mk (e ≫ p)))
    (D.res_comp_map f₂ (Under.homMk p : Under.mk e ⟶ Under.mk (e ≫ p)))

private lemma leibnizSlice_fst :
    D.leibnizSlice f₂ p e ≫ pullback.fst _ _ = D.res f₂ (Under.mk e) :=
  pullback.lift_fst _ _ _

private lemma leibnizSlice_snd :
    D.leibnizSlice f₂ p e ≫ pullback.snd _ _ =
      (D.R Y₂).map (Under.homMk p : Under.mk e ⟶ Under.mk (e ≫ p)) :=
  pullback.lift_snd _ _ _

variable {X₁ Y₁ : 𝒞} {f₁ : X₁ ⟶ Y₁} {f₂}

private lemma hasLift_of_forall_hasLift (sq : F.PushoutObjObj f₁ f₂) {u : sq.pt ⟶ E}
    {v : (F.obj Y₁).obj Y₂ ⟶ S} (hsq : CommSq u sq.ι p v)
    (h : ∀ (a : X₁ ⟶ (D.R Y₂).obj (Under.mk (incl X₁ Y₂ ≫ sq.inr ≫ u)))
      (b : Y₁ ⟶ _),
      ∀ hab : CommSq a f₁ (D.leibnizSlice f₂ p (incl X₁ Y₂ ≫ sq.inr ≫ u)) b, hab.HasLift) :
    hsq.HasLift := by
  let e := incl X₁ Y₂ ≫ sq.inr ≫ u
  have h₁ : incl Y₁ X₂ ≫ sq.inl ≫ u = f₂ ≫ e := by
    rw [← hincl f₁ X₂, Category.assoc, ← Category.assoc _ sq.inl, sq.isPushout.w,
      Category.assoc, ← Category.assoc (incl X₁ X₂), D.incl_comp_map, Category.assoc]
  have h₃ : incl Y₁ Y₂ ≫ v = e ≫ p := by
    rw [← hincl f₁ Y₂, Category.assoc, ← sq.inr_ι, Category.assoc, ← hsq.w]
    simp only [e, Category.assoc]
  let a := D.untranspose (t := Under.mk e) (sq.inr ≫ u) rfl
  let c := D.untranspose (t := Under.mk (f₂ ≫ e)) (sq.inl ≫ u) h₁
  let b := D.untranspose (t := Under.mk (e ≫ p)) v h₃
  have hcb : c ≫ (D.R X₂).map (Under.homMk p (by simp) :
      Under.mk (f₂ ≫ e) ⟶ Under.mk (f₂ ≫ e ≫ p)) = b ≫ D.res f₂ (Under.mk (e ≫ p)) := by
    apply D.transpose_injective
    rw [transpose_comp_map_homMk, transpose_comp_res, transpose_untranspose,
      transpose_untranspose]
    exact (Category.assoc _ _ _).trans ((congrArg _ hsq.w).trans (sq.inl_ι_assoc v))
  have hsq' : CommSq a f₁ (D.leibnizSlice f₂ p e) (pullback.lift c b hcb) := ⟨by
    apply pullback.hom_ext
    · simp only [Category.assoc, leibnizSlice_fst, pullback.lift_fst]
      apply D.transpose_injective
      rw [transpose_comp_res, transpose_comp, transpose_untranspose, transpose_untranspose]
      exact (Category.assoc _ _ _).symm.trans ((sq.isPushout.w =≫ u).symm.trans
        (Category.assoc _ _ _))
    · simp only [Category.assoc, leibnizSlice_snd, pullback.lift_snd]
      apply D.transpose_injective
      rw [transpose_comp_map_homMk, transpose_comp, transpose_untranspose,
        transpose_untranspose]
      exact (Category.assoc _ _ _).trans ((congrArg _ hsq.w).trans (sq.inr_ι_assoc v))⟩
  obtain ⟨l⟩ := (h a _ hsq').exists_lift
  have hc : l.l ≫ D.res f₂ (Under.mk e) = c :=
    calc l.l ≫ D.res f₂ (Under.mk e) = l.l ≫ D.leibnizSlice f₂ p e ≫ pullback.fst _ _ := by
          rw [leibnizSlice_fst]
      _ = c := by rw [← Category.assoc l.l, l.fac_right, pullback.lift_fst]
  have hb : l.l ≫ (D.R Y₂).map (Under.homMk p : Under.mk e ⟶ Under.mk (e ≫ p)) = b :=
    calc _ = l.l ≫ D.leibnizSlice f₂ p e ≫ pullback.snd _ _ := by rw [leibnizSlice_snd]
      _ = b := by rw [← Category.assoc l.l, l.fac_right, pullback.lift_snd]
  refine ⟨⟨⟨D.transpose l.l, sq.hom_ext ?_ ?_, ?_⟩⟩⟩
  · rw [sq.inl_ι_assoc, ← transpose_comp_res, hc, transpose_untranspose]
  · rw [sq.inr_ι_assoc, ← transpose_comp, l.fac_left, transpose_untranspose]
  · exact (D.transpose_comp_map_homMk (t' := Under.mk (e ≫ p)) l.l p rfl).symm.trans
      ((congrArg D.transpose hb).trans (D.transpose_untranspose _ _))

private lemma hasLiftingProperty_leibnizSlice_iff (sq : F.PushoutObjObj f₁ f₂) :
    HasLiftingProperty f₁ (D.leibnizSlice f₂ p e) ↔
      ∀ {u : sq.pt ⟶ E} {v : (F.obj Y₁).obj Y₂ ⟶ S} (hsq : CommSq u sq.ι p v),
        incl X₁ Y₂ ≫ sq.inr ≫ u = e → hsq.HasLift := by
  refine ⟨fun h u v hsq he ↦ ?_, fun h ↦ ⟨fun {a w} hsq ↦ ?_⟩⟩
  · subst he
    exact D.hasLift_of_forall_hasLift p sq hsq fun _ _ hab ↦ h.sq_hasLift hab
  have hw : (F.map f₁).app X₂ ≫ D.transpose (w ≫ pullback.fst _ _) =
      (F.obj X₁).map f₂ ≫ D.transpose a := by
    rw [← transpose_comp, ← Category.assoc, ← hsq.w, Category.assoc, leibnizSlice_fst,
      transpose_comp_res]
  let u : sq.pt ⟶ E := sq.isPushout.desc _ _ hw
  let v : (F.obj Y₁).obj Y₂ ⟶ S := D.transpose (w ≫ pullback.snd _ _)
  have hl : sq.inl ≫ u ≫ p = sq.inl ≫ sq.ι ≫ v :=
    calc sq.inl ≫ u ≫ p = D.transpose (w ≫ pullback.fst _ _) ≫ p := by
          rw [sq.isPushout.inl_desc_assoc]
      _ = D.transpose ((w ≫ pullback.fst _ _) ≫ (D.R X₂).map (Under.homMk p (by simp) :
          Under.mk (f₂ ≫ e) ⟶ Under.mk (f₂ ≫ e ≫ p))) :=
        (D.transpose_comp_map_homMk (t' := Under.mk (f₂ ≫ e ≫ p)) (w ≫ pullback.fst _ _) p
          (by simp)).symm
      _ = D.transpose ((w ≫ pullback.snd _ _) ≫ D.res f₂ (Under.mk (e ≫ p))) := by
        rw [Category.assoc w, Category.assoc w, pullback.condition]
      _ = sq.inl ≫ sq.ι ≫ v := (D.transpose_comp_res f₂ _).trans (sq.inl_ι_assoc v).symm
  have hr : sq.inr ≫ u ≫ p = sq.inr ≫ sq.ι ≫ v :=
    calc sq.inr ≫ u ≫ p = D.transpose a ≫ p := by rw [sq.isPushout.inr_desc_assoc]
      _ = D.transpose (a ≫ (D.R Y₂).map (Under.homMk p : Under.mk e ⟶ Under.mk (e ≫ p))) :=
        (D.transpose_comp_map_homMk (t' := Under.mk (e ≫ p)) a p rfl).symm
      _ = D.transpose (f₁ ≫ w ≫ pullback.snd _ _) := by
        rw [← leibnizSlice_snd, ← Category.assoc a, hsq.w, Category.assoc f₁]
      _ = sq.inr ≫ sq.ι ≫ v := (D.transpose_comp f₁ _).trans (sq.inr_ι_assoc v).symm
  obtain ⟨l⟩ := (h (⟨sq.hom_ext hl hr⟩ : CommSq u sq.ι p v) (by
    rw [sq.isPushout.inr_desc, incl_comp_transpose]
    rfl)).exists_lift
  have hl : incl Y₁ Y₂ ≫ l.l = (Under.mk e).hom := by
    rw [← hincl f₁ Y₂, Category.assoc, ← sq.inr_ι, Category.assoc, l.fac_left,
      sq.isPushout.inr_desc, incl_comp_transpose]
  refine ⟨⟨⟨D.untranspose l.l hl, D.transpose_injective ?_, pullback.hom_ext
    (D.transpose_injective ?_) (D.transpose_injective ?_)⟩⟩⟩
  · rw [transpose_comp, transpose_untranspose, ← sq.inr_ι_assoc, l.fac_left,
      sq.isPushout.inr_desc]
  · rw [Category.assoc, leibnizSlice_fst, transpose_comp_res, transpose_untranspose,
      ← sq.inl_ι_assoc, l.fac_left, sq.isPushout.inl_desc]
  · rw [Category.assoc, leibnizSlice_snd, transpose_comp_map_homMk, transpose_untranspose,
      l.fac_right]

variable {p} in
private lemma hasLiftingProperty_ι_iff (sq : F.PushoutObjObj f₁ f₂) :
    HasLiftingProperty sq.ι p ↔ ∀ e : Y₂ ⟶ E, HasLiftingProperty f₁ (D.leibnizSlice f₂ p e) :=
  ⟨fun h e ↦ (D.hasLiftingProperty_leibnizSlice_iff p e sq).2 fun hsq _ ↦ h.sq_hasLift hsq,
    fun h ↦ ⟨fun hsq ↦ (D.hasLiftingProperty_leibnizSlice_iff p _ sq).1 (h _) hsq rfl⟩⟩

end UnderAdjoints

end Leibniz

variable {C : Type w} [SmallCategory C] [MonoidalCategory (WithInitial C)]
  [∀ P Q : (WithInitial C)ᵒᵖ ⥤ Type (max w u), MonoidalCategory.DayConvolution P Q]
  [TensorUnitIsStar C]

private noncomputable def joinRightUnderAdjoints :
    UnderAdjoints (Functor.curry.obj (joinFunctor.{w, u} (C := C))) joinInclRight
      (fun f B ↦ (joinInclRight_comp_joinMap f (𝟙 B)).trans (Category.id_comp _)) where
  incl_comp_map X _ _ g := joinInclRight_comp_joinMap (𝟙 X) g
  R := slice
  adj := joinRightUnderAdjunction

private noncomputable def joinLeftUnderAdjoints :
    UnderAdjoints (Functor.curry.obj (joinFunctor.{w, u} (C := C))).flip
      (fun Y A ↦ joinInclLeft A Y)
      (fun g A ↦ (joinInclLeft_comp_joinMap (𝟙 A) g).trans (Category.id_comp _)) where
  incl_comp_map Y _ _ g := joinInclLeft_comp_joinMap g (𝟙 Y)
  R := coslice
  adj := joinLeftUnderAdjunction

noncomputable def sliceRes {T T' : Cᵒᵖ ⥤ Type (max w u)} (g : T' ⟶ T) :
    slice.{w, u} T ⟶ Under.map g ⋙ slice T' where
  app := joinRightUnderAdjoints.res g
  naturality _ _ k := (joinRightUnderAdjoints.res_comp_map g k).symm

noncomputable def leibnizSlice {S T X Y : Cᵒᵖ ⥤ Type (max w u)} (j : S ⟶ T) (p : X ⟶ Y)
    (t : T ⟶ X) :
    (slice T).obj (Under.mk t) ⟶ pullback ((slice S).map (Under.homMk p (by simp) :
      Under.mk (j ≫ t) ⟶ Under.mk (j ≫ t ≫ p))) ((sliceRes j).app (Under.mk (t ≫ p))) :=
  joinRightUnderAdjoints.leibnizSlice j p t

@[reassoc (attr := simp)]
theorem leibnizSlice_fst {S T X Y : Cᵒᵖ ⥤ Type (max w u)} (j : S ⟶ T) (p : X ⟶ Y) (t : T ⟶ X) :
    leibnizSlice j p t ≫ pullback.fst _ _ = (sliceRes j).app (Under.mk t) :=
  joinRightUnderAdjoints.leibnizSlice_fst j p t

@[reassoc (attr := simp)]
theorem leibnizSlice_snd {S T X Y : Cᵒᵖ ⥤ Type (max w u)} (j : S ⟶ T) (p : X ⟶ Y) (t : T ⟶ X) :
    leibnizSlice j p t ≫ pullback.snd _ _ =
      (slice T).map (Under.homMk p : Under.mk t ⟶ Under.mk (t ≫ p)) :=
  joinRightUnderAdjoints.leibnizSlice_snd j p t

theorem hasLiftingProperty_leibnizSlice_iff {K L S T X Y : Cᵒᵖ ⥤ Type (max w u)} {i : K ⟶ L}
    {j : S ⟶ T} (sq : (Functor.curry.obj joinFunctor).PushoutObjObj i j) (p : X ⟶ Y)
    (t : T ⟶ X) :
    HasLiftingProperty i (leibnizSlice j p t) ↔
      ∀ {a : sq.pt ⟶ X} {b : join L T ⟶ Y} (hsq : CommSq a sq.ι p b),
        joinInclRight K T ≫ sq.inr ≫ a = t → hsq.HasLift :=
  joinRightUnderAdjoints.hasLiftingProperty_leibnizSlice_iff p t sq

theorem hasLiftingProperty_pushoutObjObj_ι_iff {K L S T X Y : Cᵒᵖ ⥤ Type (max w u)}
    {i : K ⟶ L} {j : S ⟶ T} (sq : (Functor.curry.obj joinFunctor).PushoutObjObj i j)
    (p : X ⟶ Y) :
    HasLiftingProperty sq.ι p ↔ ∀ t : T ⟶ X, HasLiftingProperty i (leibnizSlice j p t) :=
  joinRightUnderAdjoints.hasLiftingProperty_ι_iff sq

theorem sliceRes_comp {A B T : Cᵒᵖ ⥤ Type (max w u)} (a : A ⟶ B) (b : B ⟶ T) (t : Under T) :
    (sliceRes b).app t ≫ (sliceRes a).app ((Under.map b).obj t) = (sliceRes (a ≫ b)).app t := by
  refine (joinRightUnderAdjoints.res_comp a b t).trans ?_
  have : (Under.homMk (𝟙 _) (by simp) :
      Under.mk ((a ≫ b) ≫ t.hom) ⟶ Under.mk (a ≫ b ≫ t.hom)) = 𝟙 _ := rfl
  rw [this]
  exact (congrArg (_ ≫ ·) ((slice A).map_id _)).trans (Category.comp_id _)

theorem sliceRes_id (T : Cᵒᵖ ⥤ Type (max w u)) (t : Under T) :
    (sliceRes (𝟙 T)).app t = 𝟙 _ :=
  (joinRightUnderAdjoints.res_id t).trans ((slice T).map_id t)

private lemma sliceObjEquiv_app_coe {T P : Cᵒᵖ ⥤ Type (max w u)} {t : Under T}
    (ψ : P ⟶ (slice T).obj t) (c : C) (x : P.obj (Opposite.op c)) :
    (sliceObjEquiv T t c (ψ.app (Opposite.op c) x)).1 =
      joinMap (uliftYonedaEquiv.symm x) (𝟙 T) ≫ joinRightUnderAdjoints.transpose ψ := by
  have : PreservesColimitsOfSize.{w, max w u} (joinRightUnder T) :=
    preservesColimitsOfSize_shrink _
  have := Presheaf.isLeftKanExtension_of_preservesColimits.{0} (joinRightUnder T) (Iso.refl _)
  have h := (congrArg (fun f ↦ f.app (Opposite.op c) x)
    (((joinRightUnderAdjunction T).homEquiv _ _).apply_symm_apply ψ)).symm.trans
      (Presheaf.uliftYonedaAdjunction_homEquiv_app.{0} (joinRightUnder T) (Iso.refl _).hom
        (((joinRightUnderAdjunction T).homEquiv _ _).symm ψ) x)
  rw [h]
  exact congrArg Under.Hom.right (Category.id_comp _)

theorem sliceObjEquiv_sliceRes_app_app_coe {T T' : Cᵒᵖ ⥤ Type (max w u)} (g : T' ⟶ T)
    (t : Under T) (c : C) (x : ((slice T).obj t).obj (Opposite.op c)) :
    (sliceObjEquiv T' ((Under.map g).obj t) c (((sliceRes g).app t).app (Opposite.op c) x)).1 =
      joinMap (𝟙 _) g ≫ (sliceObjEquiv T t c x).1 := by
  have hx := sliceObjEquiv_app_coe (𝟙 ((slice T).obj t)) c x
  rw [NatTrans.id_app, types_id_apply] at hx
  rw [sliceObjEquiv_app_coe, hx]
  exact (congrArg (joinMap (uliftYonedaEquiv.symm x) (𝟙 T') ≫ ·)
    (joinRightUnderAdjoints.transpose_res g t)).trans (joinMap_exchange_assoc _ _ _).symm

noncomputable def isTerminalSliceObj {T : Cᵒᵖ ⥤ Type (max w u)} (t : Under T)
    (ht : IsTerminal t.right) : IsTerminal ((slice T).obj t) :=
  have := (joinRightUnderAdjunction T).rightAdjoint_preservesLimits
  IsTerminal.isTerminalObj (slice T) t (IsTerminal.ofUniqueHom
    (fun Y ↦ Under.homMk (ht.from Y.right) (ht.hom_ext _ _))
    (fun _ _ ↦ Under.UnderMorphism.ext (ht.hom_ext _ _)))

noncomputable def cosliceRes {T T' : Cᵒᵖ ⥤ Type (max w u)} (g : T' ⟶ T) :
    coslice.{w, u} T ⟶ Under.map g ⋙ coslice T' where
  app := joinLeftUnderAdjoints.res g
  naturality _ _ k := (joinLeftUnderAdjoints.res_comp_map g k).symm

noncomputable def leibnizCoslice {S T X Y : Cᵒᵖ ⥤ Type (max w u)} (j : S ⟶ T) (p : X ⟶ Y)
    (t : T ⟶ X) :
    (coslice T).obj (Under.mk t) ⟶ pullback ((coslice S).map (Under.homMk p (by simp) :
      Under.mk (j ≫ t) ⟶ Under.mk (j ≫ t ≫ p))) ((cosliceRes j).app (Under.mk (t ≫ p))) :=
  joinLeftUnderAdjoints.leibnizSlice j p t

theorem hasLiftingProperty_leibnizCoslice_iff {K L S T X Y : Cᵒᵖ ⥤ Type (max w u)}
    {i : K ⟶ L} {j : S ⟶ T} (sq : (Functor.curry.obj joinFunctor).PushoutObjObj j i)
    (p : X ⟶ Y) (t : T ⟶ X) :
    HasLiftingProperty i (leibnizCoslice j p t) ↔
      ∀ {a : sq.pt ⟶ X} {b : join T L ⟶ Y} (hsq : CommSq a sq.ι p b),
        joinInclLeft T K ≫ sq.inl ≫ a = t → hsq.HasLift :=
  joinLeftUnderAdjoints.hasLiftingProperty_leibnizSlice_iff p t sq.flip

theorem cosliceRes_comp {A B T : Cᵒᵖ ⥤ Type (max w u)} (a : A ⟶ B) (b : B ⟶ T) (t : Under T) :
    (cosliceRes b).app t ≫ (cosliceRes a).app ((Under.map b).obj t) =
      (cosliceRes (a ≫ b)).app t := by
  refine (joinLeftUnderAdjoints.res_comp a b t).trans ?_
  have : (Under.homMk (𝟙 _) (by simp) :
      Under.mk ((a ≫ b) ≫ t.hom) ⟶ Under.mk (a ≫ b ≫ t.hom)) = 𝟙 _ := rfl
  rw [this]
  exact (congrArg (_ ≫ ·) ((coslice A).map_id _)).trans (Category.comp_id _)

theorem cosliceRes_id (T : Cᵒᵖ ⥤ Type (max w u)) (t : Under T) :
    (cosliceRes (𝟙 T)).app t = 𝟙 _ :=
  (joinLeftUnderAdjoints.res_id t).trans ((coslice T).map_id t)

theorem homEquiv_symm_comp_cosliceRes_app_right {T T' P : Cᵒᵖ ⥤ Type (max w u)} (g : T' ⟶ T)
    {t : Under T} (ψ : P ⟶ (coslice T).obj t) :
    (((joinLeftUnderAdjunction T').homEquiv _ _).symm (ψ ≫ (cosliceRes g).app t)).right =
      joinMap g (𝟙 P) ≫ (((joinLeftUnderAdjunction T).homEquiv _ _).symm ψ).right :=
  joinLeftUnderAdjoints.transpose_comp_res g ψ

theorem isIso_cosliceRes_app {T T' : Cᵒᵖ ⥤ Type (max w u)} (g : T' ⟶ T) [IsIso g]
    (t : Under T) : IsIso ((cosliceRes g).app t) := by
  have hid : ∀ {S : Cᵒᵖ ⥤ Type (max w u)} (h : S ⟶ S) (s : Under S), h = 𝟙 S →
      IsIso ((cosliceRes h).app s) := by
    rintro S _ s rfl
    rw [cosliceRes_id]
    exact IsIso.id _
  have h₁ : IsIso ((cosliceRes g).app t ≫ (cosliceRes (inv g)).app ((Under.map g).obj t)) := by
    rw [cosliceRes_comp]
    exact hid _ _ (IsIso.inv_hom_id g)
  have h₂ : IsIso ((cosliceRes (inv g)).app ((Under.map g).obj t) ≫
      (cosliceRes g).app ((Under.map (inv g)).obj ((Under.map g).obj t))) := by
    rw [cosliceRes_comp]
    exact hid _ _ (IsIso.hom_inv_id g)
  have : IsSplitEpi ((cosliceRes (inv g)).app ((Under.map g).obj t)) :=
    IsSplitEpi.mk' ⟨inv ((cosliceRes g).app t ≫ (cosliceRes (inv g)).app ((Under.map g).obj t)) ≫
      (cosliceRes g).app t, by rw [Category.assoc, IsIso.inv_hom_id]⟩
  have : Mono ((cosliceRes (inv g)).app ((Under.map g).obj t)) := mono_of_mono _
    ((cosliceRes g).app ((Under.map (inv g)).obj ((Under.map g).obj t)))
  have : IsIso ((cosliceRes (inv g)).app ((Under.map g).obj t)) := isIso_of_mono_of_isSplitEpi _
  exact IsIso.of_isIso_comp_right _ ((cosliceRes (inv g)).app ((Under.map g).obj t))

end CategoryTheory.WithInitial
