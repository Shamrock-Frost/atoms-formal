import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.TwoTruncated
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Left
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.JoinSlice
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj

open CategoryTheory Limits Simplicial Opposite HomotopicalAlgebra MorphismProperty
open AugmentedSimplexCategory (inl'_eq_δ_last)

universe u

namespace SSet

inductive rightHornInclusions : MorphismProperty SSet.{u} where
  | intro {n : ℕ} (i : Fin (n + 2)) (h0 : 0 < i) : rightHornInclusions Λ[n + 1, i].ι

def rightFibrations : MorphismProperty SSet.{u} := rightHornInclusions.rlp

def rightAnodyneExtensions : MorphismProperty SSet.{u} := rightFibrations.llp
deriving RespectsIso

theorem innerFibration_of_rightFibrations {X Y : SSet.{u}} {p : X ⟶ Y}
    (hp : rightFibrations p) : InnerFibration p :=
  ⟨antitone_rlp (fun _ _ _ ⟨i, h0, _⟩ ↦ ⟨i, h0⟩) _ hp⟩

theorem horn_ι_mem_rightHornInclusions {n : ℕ} {i : Fin (n + 1)} (h0 : 0 < i) :
    rightHornInclusions.{u} Λ[n, i].ι := by
  obtain _ | n := n
  · exact absurd h0 (by simp [Fin.lt_def])
  · exact .intro i h0

theorem rightAnodyneExtensions.horn_ι {n : ℕ} {i : Fin (n + 1)} (h0 : 0 < i) :
    rightAnodyneExtensions.{u} Λ[n, i].ι :=
  le_llp_rlp _ _ (horn_ι_mem_rightHornInclusions h0)

theorem innerAnodyneExtensions_le_rightAnodyneExtensions :
    innerAnodyneExtensions.{u} ≤ rightAnodyneExtensions := by
  rw [innerAnodyneExtensions_eq_llp_rlp]
  refine antitone_llp (antitone_rlp ?_)
  rintro _ _ _ ⟨i, h0, -⟩
  exact .intro i h0

theorem rightHornInclusions_le_J : rightHornInclusions.{u} ≤ modelCategoryQuillen.J :=
  fun _ _ _ ⟨_, _⟩ ↦ modelCategoryQuillen.horn_ι_mem_J ..

theorem rightHornInclusions_le_monomorphisms :
    rightHornInclusions.{u} ≤ MorphismProperty.monomorphisms SSet :=
  fun _ _ _ ⟨_, _⟩ ↦ monomorphisms.infer_property _

private lemma rightHornInclusions_eq_iSup :
    rightHornInclusions.{u} =
      ⨆ n, .ofHoms (fun p : {p : Fin (n + 2) // 0 < p} ↦ Λ[n + 1, p].ι) := by
  ext
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain @⟨n, i, h0⟩ := h
    simp only [iSup_iff, ofHoms_iff, Subtype.exists, exists_prop]
    use n, i
  · simp only [iSup_iff, ofHoms_iff] at h
    obtain ⟨n, ⟨i, h0⟩, _, _⟩ := h
    exact .intro i h0

attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

instance : MorphismProperty.IsSmall.{u} rightHornInclusions.{u} := by
  rw [rightHornInclusions_eq_iSup]
  have (n : ℕ) : MorphismProperty.IsSmall.{u}
      (MorphismProperty.ofHoms.{u} fun p : {p : Fin (n + 2) // 0 < p} ↦ Λ[n + 1, p].ι) :=
    isSmall_ofHoms ..
  exact isSmall_iSup _

instance : IsCardinalForSmallObjectArgument rightHornInclusions.{u} Cardinal.aleph0.{u} where
  preservesColimit {A B X Y} i hi f hf := by
    have : IsFinitelyPresentable.{u} A := by
      simp only [rightHornInclusions_eq_iSup, iSup_iff] at hi
      obtain ⟨n, ⟨i⟩⟩ := hi
      infer_instance
    infer_instance

instance : HasSmallObjectArgument.{u} rightHornInclusions.{u} where
  exists_cardinal := ⟨.aleph0, inferInstance, inferInstance, inferInstance⟩

theorem exists_simplex_of_hasLiftingProperty_horn {E B : SSet.{u}} (q : E ⟶ B) {n : ℕ}
    {i : Fin (n + 2)} [HasLiftingProperty Λ[n + 1, i].ι q] (s : ∀ j : Fin (n + 2), j ≠ i → E _⦋n⦌)
    (hc : horn.IsCompatible (fun j hj ↦ yonedaEquiv.symm (s j hj)))
    (τ : B _⦋n + 1⦌) (hτ : ∀ (j : Fin (n + 2)) (hj : j ≠ i), B.δ j τ = q.app _ (s j hj)) :
    ∃ σ : E _⦋n + 1⦌, (∀ (j : Fin (n + 2)) (hj : j ≠ i), E.δ j σ = s j hj) ∧ q.app _ σ = τ := by
  have hsq : CommSq hc.desc Λ[n + 1, i].ι q (yonedaEquiv.symm τ) := ⟨horn.hom_ext' fun j hj ↦ by
    rw [hc.ι_desc_assoc, horn.ι_ι_assoc, stdSimplex.δ_comp_yonedaEquiv_symm, hτ j hj,
      ← yonedaEquiv_symm_comp]⟩
  refine ⟨yonedaEquiv hsq.lift, fun j hj ↦ ?_, ?_⟩
  · rw [← stdSimplex.yonedaEquiv_δ_comp, ← horn.ι_ι i j hj, Category.assoc, hsq.fac_left,
      hc.ι_desc, Equiv.apply_symm_apply]
  · rw [← yonedaEquiv_comp, hsq.fac_right, Equiv.apply_symm_apply]

theorem exists_compStruct_id_of_hasLiftingProperty {E B : SSet.{u}} (q : E ⟶ B)
    [HasLiftingProperty Λ[2, 2].ι q] {x y : E _⦋0⦌} (e : Edge y x) (τ : B _⦋2⦌)
    (h₀ : B.δ 0 τ = q.app _ e.edge) (h₁ : B.δ 1 τ = q.app _ (E.σ 0 x)) :
    ∃ e' : Edge x y, Nonempty (Edge.CompStruct e' e (Edge.id x)) ∧
      q.app _ e'.edge = B.δ 2 τ := by
  obtain ⟨σ, hσ, hqσ⟩ := exists_simplex_of_hasLiftingProperty_horn q (i := 2)
    (fun j _ ↦ ![e.edge, E.σ 0 x, E.σ 0 x] j) (fun j k hj hk hjk ↦ by
      fin_cases j <;> fin_cases k
      all_goals try exact absurd hjk (by decide)
      all_goals try exact (hk rfl).elim
      simp only [stdSimplex.δ_comp_yonedaEquiv_symm]
      exact congrArg _ ((Edge.tgt_eq e).trans (δ_comp_σ_self_apply (S := E) 0 x).symm))
    τ (fun j hj ↦ by
      fin_cases j
      · exact h₀
      · exact h₁
      · exact (hj rfl).elim)
  have h₀' : E.δ 0 σ = e.edge := hσ 0 (by decide)
  have h₁' : E.δ 1 σ = E.σ 0 x := hσ 1 (by decide)
  refine ⟨Edge.mk (E.δ 2 σ) ((δ_comp_δ_self_apply (i := 1) σ).symm.trans
    ((congrArg _ h₁').trans (δ_comp_σ_succ_apply (S := E) 0 x)))
    ((δ_comp_δ_apply (i := 0) (j := 1) (by decide) σ).trans
      ((congrArg _ h₀').trans (Edge.src_eq e))), ⟨Edge.CompStruct.mk σ rfl h₀' h₁'⟩,
    (δ_naturality_apply q 2 σ).trans (congrArg (B.δ 2) hqσ)⟩

theorem exists_edge_map_eq_of_rightFibrations {E B : SSet.{u}} {q : E ⟶ B}
    (hq : rightFibrations q) {x₀ : E _⦋0⦌} {y₁ : B _⦋0⦌} (g : Edge (q.app _ x₀) y₁)
    (hg : Nonempty g.InvStruct) : ∃ (x₁ : E _⦋0⦌) (f : Edge x₀ x₁), (f.map q).edge = g.edge := by
  obtain ⟨I⟩ := hg
  have : HasLiftingProperty Λ[1, 1].ι q := hq _ (horn_ι_mem_rightHornInclusions (by decide))
  have : HasLiftingProperty Λ[2, 2].ι q := hq _ (horn_ι_mem_rightHornInclusions (by decide))
  obtain ⟨β, hβ, hqβ⟩ := exists_simplex_of_hasLiftingProperty_horn q (i := 1) (fun _ _ ↦ x₀)
    trivial I.inv.edge (fun j hj ↦ by
      fin_cases j
      · exact Edge.tgt_eq I.inv
      · exact (hj rfl).elim)
  obtain ⟨f, -, hf⟩ := exists_compStruct_id_of_hasLiftingProperty q
    (Edge.mk β rfl (hβ 0 (by decide))) I.homInvId.simplex (I.homInvId.d₀.trans hqβ.symm)
    (I.homInvId.d₁.trans (σ_naturality_apply q 0 x₀).symm)
  exact ⟨_, f, hf.trans I.homInvId.d₂⟩

theorem nonempty_invStruct_of_rightFibrations {P Z : SSet.{u}} {r : P ⟶ Z}
    (hr : rightFibrations r) [P.Quasicategory] {x₀ x₁ : P _⦋0⦌} (f : Edge x₀ x₁)
    (h : Nonempty (f.map r).InvStruct) : Nonempty f.InvStruct := by
  obtain ⟨I⟩ := h
  have : HasLiftingProperty Λ[2, 2].ι r := hr _ (horn_ι_mem_rightHornInclusions (by decide))
  obtain ⟨β, ⟨hβ⟩, hrβ⟩ := exists_compStruct_id_of_hasLiftingProperty r f
    I.invHomId.simplex I.invHomId.d₀ (I.invHomId.d₁.trans (σ_naturality_apply r 0 x₁).symm)
  obtain ⟨γ, ⟨hγ⟩, -⟩ := exists_compStruct_id_of_hasLiftingProperty r β
    I.homInvId.simplex (I.homInvId.d₀.trans (hrβ.trans I.invHomId.d₂).symm)
    (I.homInvId.d₁.trans (σ_naturality_apply r 0 x₀).symm)
  have h₁ := (Truncated.HomotopyCategory.homMk_comp_homMk hβ).trans
    (Truncated.HomotopyCategory.homMk_id _)
  have h₂ := (Truncated.HomotopyCategory.homMk_comp_homMk hγ).trans
    (Truncated.HomotopyCategory.homMk_id _)
  have hγf : Truncated.HomotopyCategory.homMk γ.toTruncated =
      Truncated.HomotopyCategory.homMk f.toTruncated := by
    rw [← Category.comp_id (Truncated.HomotopyCategory.homMk γ.toTruncated), ← h₁,
      ← Category.assoc, h₂, Category.id_comp]
  rw [← isIso_homMk_iff]
  exact ⟨Truncated.HomotopyCategory.homMk β.toTruncated,
    (congrArg (· ≫ Truncated.HomotopyCategory.homMk β.toTruncated) hγf.symm).trans h₂, h₁⟩

theorem hasLift_horn_one_zero_of_rightFibrations {E B : SSet.{u}} {q : E ⟶ B}
    (hq : rightFibrations q) {a : (Λ[1, 0] : SSet.{u}) ⟶ E} {b : Δ[1] ⟶ B}
    (sq : CommSq a Λ[1, 0].ι q b) (h : Nonempty (Edge.mk' (yonedaEquiv b)).InvStruct) :
    sq.HasLift := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have hx : q.app _ (yonedaEquiv (horn.ι 0 1 h10 ≫ a)) = B.δ 1 (yonedaEquiv b) := by
    rw [← yonedaEquiv_comp, Category.assoc, sq.w, horn.ι_ι_assoc, stdSimplex.yonedaEquiv_δ_comp]
  obtain ⟨x₁, f, hf⟩ := exists_edge_map_eq_of_rightFibrations hq
    (Edge.mk (yonedaEquiv b) hx.symm rfl) ⟨h.some.ofEq rfl⟩
  refine ⟨⟨⟨yonedaEquiv.symm f.edge, horn.hom_ext' fun j hj ↦ ?_, yonedaEquiv.injective ?_⟩⟩⟩
  · obtain rfl : j = 1 := by
      fin_cases j
      · exact (hj rfl).elim
      · rfl
    rw [horn.ι_ι_assoc, stdSimplex.δ_comp_yonedaEquiv_symm, f.src_eq, Equiv.symm_apply_apply]
  · rw [yonedaEquiv_comp, Equiv.apply_symm_apply, ← Edge.map_edge, hf]
    rfl

section Leibniz

variable (F : SSet.{u} ⥤ SSet.{u} ⥤ SSet.{u}) (incl : ∀ X B : SSet.{u}, B ⟶ (F.obj X).obj B)
  (hincl : ∀ {X Y : SSet.{u}} (f : X ⟶ Y) (B : SSet.{u}), incl X B ≫ (F.map f).app B = incl Y B)

private def underFunctor (B : SSet.{u}) : SSet.{u} ⥤ Under B where
  obj X := Under.mk (incl X B)
  map f := Under.homMk ((F.map f).app B) (hincl f B)
  map_id X := by
    ext1
    simp
  map_comp f g := by
    ext1
    simp

private structure UnderAdjoints where
  incl_comp_map (X : SSet.{u}) {B B' : SSet.{u}} (g : B' ⟶ B) :
    incl X B' ≫ (F.obj X).map g = g ≫ incl X B
  R (B : SSet.{u}) : Under B ⥤ SSet.{u}
  adj (B : SSet.{u}) : underFunctor F incl hincl B ⊣ R B

variable {F incl hincl} (D : UnderAdjoints F incl hincl)

namespace UnderAdjoints

private def transpose {B X : SSet.{u}} {t : Under B} (ψ : X ⟶ (D.R B).obj t) :
    (F.obj X).obj B ⟶ t.right :=
  (((D.adj B).homEquiv _ _).symm ψ).right

private lemma incl_comp_transpose {B X : SSet.{u}} {t : Under B} (ψ : X ⟶ (D.R B).obj t) :
    incl X B ≫ D.transpose ψ = t.hom :=
  Under.w (((D.adj B).homEquiv _ _).symm ψ)

private def untranspose {B X : SSet.{u}} {t : Under B} (φ : (F.obj X).obj B ⟶ t.right)
    (h : incl X B ≫ φ = t.hom) : X ⟶ (D.R B).obj t :=
  (D.adj B).homEquiv _ _ (Under.homMk φ h)

private lemma transpose_untranspose {B X : SSet.{u}} {t : Under B}
    (φ : (F.obj X).obj B ⟶ t.right) (h : incl X B ≫ φ = t.hom) :
    D.transpose (D.untranspose φ h) = φ := by
  rw [transpose, untranspose, Equiv.symm_apply_apply]
  rfl

private lemma transpose_injective {B X : SSet.{u}} {t : Under B} {ψ ψ' : X ⟶ (D.R B).obj t}
    (h : D.transpose ψ = D.transpose ψ') : ψ = ψ' :=
  ((D.adj B).homEquiv _ _).symm.injective (Under.UnderMorphism.ext h)

private lemma transpose_comp {B X X' : SSet.{u}} {t : Under B} (f : X' ⟶ X)
    (ψ : X ⟶ (D.R B).obj t) : D.transpose (f ≫ ψ) = (F.map f).app B ≫ D.transpose ψ := by
  rw [transpose, Adjunction.homEquiv_naturality_left_symm, Under.comp_right]
  rfl

private lemma transpose_comp_map {B X : SSet.{u}} {t t' : Under B} (ψ : X ⟶ (D.R B).obj t)
    (k : t ⟶ t') : D.transpose (ψ ≫ (D.R B).map k) = D.transpose ψ ≫ k.right := by
  rw [transpose, Adjunction.homEquiv_naturality_right_symm, Under.comp_right]
  rfl

private def res {B B' : SSet.{u}} (g : B' ⟶ B) (t : Under B) :
    (D.R B).obj t ⟶ (D.R B').obj (Under.mk (g ≫ t.hom)) :=
  D.untranspose ((F.obj _).map g ≫ D.transpose (𝟙 _)) (by
    rw [← Category.assoc, D.incl_comp_map, Category.assoc, incl_comp_transpose]
    rfl)

private lemma transpose_comp_res {B B' X : SSet.{u}} (g : B' ⟶ B) {t : Under B}
    (ψ : X ⟶ (D.R B).obj t) :
    D.transpose (ψ ≫ D.res g t) = (F.obj X).map g ≫ D.transpose ψ := by
  rw [transpose_comp, res, transpose_untranspose, ← Category.assoc, ← NatTrans.naturality,
    Category.assoc, ← transpose_comp, Category.comp_id]

private lemma res_comp_map {B B' : SSet.{u}} (g : B' ⟶ B) {t t' : Under B} (k : t ⟶ t') :
    D.res g t ≫ (D.R B').map (Under.homMk k.right (by simp [Under.w k]) :
      Under.mk (g ≫ t.hom) ⟶ Under.mk (g ≫ t'.hom)) = (D.R B).map k ≫ D.res g t' := by
  apply D.transpose_injective
  rw [transpose_comp_map, transpose_comp_res, ← Category.id_comp ((D.R B).map k),
    transpose_comp_map, res, transpose_untranspose, Category.assoc]
  rfl

variable {X₂ Y₂ E S : SSet.{u}} (f₂ : X₂ ⟶ Y₂) (p : E ⟶ S) (e : Y₂ ⟶ E)

private noncomputable abbrev leibnizSliceTarget : SSet.{u} :=
  pullback ((D.R X₂).map (Under.homMk p (by simp) :
    Under.mk (f₂ ≫ e) ⟶ Under.mk (f₂ ≫ e ≫ p))) (D.res f₂ (Under.mk (e ≫ p)))

private noncomputable def leibnizSlice :
    (D.R Y₂).obj (Under.mk e) ⟶ D.leibnizSliceTarget f₂ p e :=
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

variable {X₁ Y₁ : SSet.{u}} {f₁ : X₁ ⟶ Y₁} {f₂}

private lemma transpose_comp_map_homMk {B X : SSet.{u}} {t t' : Under B} (ψ : X ⟶ (D.R B).obj t)
    (k : t.right ⟶ t'.right) (hk : t.hom ≫ k = t'.hom) :
    D.transpose (ψ ≫ (D.R B).map (Under.homMk k hk)) = D.transpose ψ ≫ k :=
  D.transpose_comp_map ψ _

private lemma res_comp {A B T : SSet.{u}} (a : A ⟶ B) (b : B ⟶ T) (t : Under T) :
    D.res b t ≫ D.res a (Under.mk (b ≫ t.hom)) = D.res (a ≫ b) t ≫
      (D.R A).map (Under.homMk (𝟙 _) (by simp) :
        Under.mk ((a ≫ b) ≫ t.hom) ⟶ Under.mk (a ≫ b ≫ t.hom)) := by
  apply D.transpose_injective
  rw [transpose_comp_res, transpose_comp_map_homMk, Category.comp_id,
    ← Category.id_comp (D.res b t), ← Category.id_comp (D.res (a ≫ b) t), transpose_comp_res,
    transpose_comp_res, Functor.map_comp, Category.assoc]

private lemma hasLift_of_forall_hasLift (sq : F.PushoutObjObj f₁ f₂) {u : sq.pt ⟶ E}
    {v : (F.obj Y₁).obj Y₂ ⟶ S} (hsq : CommSq u sq.ι p v)
    (h : ∀ (a : X₁ ⟶ (D.R Y₂).obj (Under.mk (incl X₁ Y₂ ≫ sq.inr ≫ u)))
      (b : Y₁ ⟶ D.leibnizSliceTarget f₂ p (incl X₁ Y₂ ≫ sq.inr ≫ u)),
      D.transpose (b ≫ pullback.fst _ _) = sq.inl ≫ u →
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
  obtain ⟨l⟩ := (h a _ ((congrArg D.transpose (pullback.lift_fst _ _ _)).trans
    (D.transpose_untranspose _ _)) hsq').exists_lift
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

private lemma hasLiftingProperty_ι (sq : F.PushoutObjObj f₁ f₂)
    (h : ∀ e : Y₂ ⟶ E, HasLiftingProperty f₁ (D.leibnizSlice f₂ p e)) :
    HasLiftingProperty sq.ι p :=
  ⟨fun hsq ↦ D.hasLift_of_forall_hasLift p sq hsq fun _ _ _ hab ↦ (h _).sq_hasLift hab⟩

private lemma hasLiftingProperty_leibnizSlice_iff (sq : F.PushoutObjObj f₁ f₂) :
    HasLiftingProperty f₁ (D.leibnizSlice f₂ p e) ↔
      ∀ {u : sq.pt ⟶ E} {v : (F.obj Y₁).obj Y₂ ⟶ S} (hsq : CommSq u sq.ι p v),
        incl X₁ Y₂ ≫ sq.inr ≫ u = e → hsq.HasLift := by
  refine ⟨fun h u v hsq he ↦ ?_, fun h ↦ ⟨fun {a w} hsq ↦ ?_⟩⟩
  · subst he
    exact D.hasLift_of_forall_hasLift p sq hsq fun _ _ _ hab ↦ h.sq_hasLift hab
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

private lemma hasLiftingProperty_leibnizSlice (sq : F.PushoutObjObj f₁ f₂)
    (h : HasLiftingProperty sq.ι p) :
    HasLiftingProperty f₁ (D.leibnizSlice f₂ p e) :=
  (D.hasLiftingProperty_leibnizSlice_iff p e sq).2 fun hsq _ ↦ h.sq_hasLift hsq

section Joyal

variable {B₀ : SSet.{u}} (ε : ∀ X : SSet.{u}, X ≅ (F.obj X).obj B₀)
  (hε : ∀ {X X' : SSet.{u}} (f : X ⟶ X'), f ≫ (ε X').hom = (ε X).hom ≫ (F.map f).app B₀)
  (hB₀ : ∀ {Z : SSet.{u}} (a b : B₀ ⟶ Z), a = b)

private def toR (t : Under B₀) : t.right ⟶ (D.R B₀).obj t :=
  D.untranspose (ε t.right).inv (hB₀ _ _)

private lemma transpose_toR (t : Under B₀) : D.transpose (D.toR ε hB₀ t) = (ε t.right).inv :=
  D.transpose_untranspose _ _

include hε in
private lemma isIso_toR (t : Under B₀) : IsIso (D.toR ε hB₀ t) := by
  refine ⟨(ε _).hom ≫ D.transpose (𝟙 _), ?_, D.transpose_injective ?_⟩
  · rw [← Category.assoc, hε, Category.assoc, ← transpose_comp, Category.comp_id, transpose_toR,
      Iso.hom_inv_id]
  · rw [transpose_comp, transpose_toR, ← cancel_epi (ε _).hom, ← Category.assoc, ← hε,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable {X₂ Y₂ E S : SSet.{u}} {f₂ : X₂ ⟶ Y₂} {p : E ⟶ S} (g₀ : B₀ ⟶ X₂)

include hε hB₀ in
private lemma hasLift_of_invStruct [E.Quasicategory]
    (hq : ∀ e : Y₂ ⟶ E, rightFibrations (D.leibnizSlice f₂ p e))
    (hres₁ : ∀ t : Y₂ ⟶ S, rightFibrations (D.res f₂ (Under.mk t)))
    (hres₀ : ∀ t : X₂ ⟶ E, rightFibrations (D.res g₀ (Under.mk t)))
    (sq : F.PushoutObjObj Λ[1, 0].ι f₂) {u : sq.pt ⟶ E} {v : (F.obj Δ[1]).obj Y₂ ⟶ S}
    (hsq : CommSq u sq.ι p v)
    (h : Nonempty (Edge.mk' (yonedaEquiv
      ((ε Δ[1]).hom ≫ (F.obj Δ[1]).map g₀ ≫ sq.inl ≫ u))).InvStruct) :
    hsq.HasLift := by
  refine D.hasLift_of_forall_hasLift p sq hsq fun a b hb hab ↦ ?_
  generalize incl _ Y₂ ≫ sq.inr ≫ u = e at a b hb hab
  obtain ⟨r, hr⟩ : ∃ r : D.leibnizSliceTarget f₂ p e ⟶ (D.R B₀).obj (Under.mk (g₀ ≫ f₂ ≫ e)),
      r = pullback.fst _ _ ≫ D.res g₀ (Under.mk (f₂ ≫ e)) := ⟨_, rfl⟩
  have hr' : rightFibrations r := hr ▸ rightHornInclusions.rlp.comp_mem _ _
    (MorphismProperty.pullback_fst _ _ (hres₁ _)) (hres₀ _)
  have := D.isIso_toR ε hε hB₀ (Under.mk (g₀ ≫ f₂ ≫ e))
  have : InnerFibration (inv (D.toR ε hB₀ (Under.mk (g₀ ≫ f₂ ≫ e)))) :=
    ⟨rlp_of_isIso _ _⟩
  have : (Under.mk (g₀ ≫ f₂ ≫ e)).right.Quasicategory := ‹E.Quasicategory›
  have := quasicategory_of_innerFibration (inv (D.toR ε hB₀ (Under.mk (g₀ ≫ f₂ ≫ e))))
  have : InnerFibration r := innerFibration_of_rightFibrations hr'
  have := quasicategory_of_innerFibration r
  have key : b ≫ r = ((ε Δ[1]).hom ≫ (F.obj Δ[1]).map g₀ ≫ sq.inl ≫ u) ≫
      D.toR ε hB₀ (Under.mk (g₀ ≫ f₂ ≫ e)) := by
    have hαε {X' : SSet.{u}} (α : Δ[1] ⟶ X') :
        (ε Δ[1]).hom ≫ (F.map α).app B₀ ≫ (ε X').inv = α := by
      rw [← Category.assoc, ← hε, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    apply D.transpose_injective
    rw [hr, ← Category.assoc b, transpose_comp_res, hb, transpose_comp, transpose_toR,
      ← cancel_epi (ε Δ[1]).hom]
    exact (hαε (X' := (Under.mk (g₀ ≫ f₂ ≫ e)).right) _).symm
  obtain ⟨I⟩ := nonempty_invStruct_of_rightFibrations hr' (Edge.mk' (yonedaEquiv b))
    ⟨(h.some.map (D.toR ε hB₀ (Under.mk (g₀ ≫ f₂ ≫ e)))).ofEq (by
      rw [Edge.map_edge, Edge.map_edge, Edge.mk'_edge, Edge.mk'_edge, ← yonedaEquiv_comp,
        ← yonedaEquiv_comp, key])⟩
  exact hasLift_horn_one_zero_of_rightFibrations (hq e) hab ⟨I⟩

end Joyal

include D in
private lemma hasLiftingProperty_ι_of_llp_rlp (W : MorphismProperty SSet.{u})
    (hf₁ : W.rlp.llp f₁) (sq : F.PushoutObjObj f₁ f₂)
    (hW : ∀ ⦃A B : SSet.{u}⦄ (h : A ⟶ B), W h →
      HasLiftingProperty (Functor.PushoutObjObj.ofHasPushout F h f₂).ι p) :
    HasLiftingProperty sq.ι p :=
  D.hasLiftingProperty_ι p sq (fun e ↦ hf₁ _ (fun _ _ h hh ↦
    D.hasLiftingProperty_leibnizSlice p e _ (hW h hh)))

private lemma hasLiftingProperty_right {B : SSet.{u}} {U V : Under B} (φ : U ⟶ V)
    (h : ∀ e : B ⟶ E, HasLiftingProperty φ (Under.homMk p : Under.mk e ⟶ Under.mk (e ≫ p))) :
    HasLiftingProperty φ.right p := by
  refine ⟨fun {u v} hsq ↦ ?_⟩
  have hv : V.hom ≫ v = (Under.mk ((U.hom ≫ u) ≫ p)).hom := by
    rw [← Under.w φ, Category.assoc, ← hsq.w]
    simp
  have hsq' : CommSq (Under.homMk u rfl : U ⟶ Under.mk (U.hom ≫ u)) φ
      (Under.homMk p : Under.mk (U.hom ≫ u) ⟶ Under.mk ((U.hom ≫ u) ≫ p))
      (Under.homMk v hv) := ⟨Under.UnderMorphism.ext hsq.w⟩
  obtain ⟨l⟩ := ((h _).sq_hasLift hsq').exists_lift
  exact ⟨⟨⟨l.l.right, congrArg Under.Hom.right l.fac_left, congrArg Under.Hom.right l.fac_right⟩⟩⟩

include D in
private lemma hasLiftingProperty_map_app_of_llp_rlp (W : MorphismProperty SSet.{u})
    (B : SSet.{u}) (hf₁ : W.rlp.llp f₁)
    (hW : ∀ ⦃A A' : SSet.{u}⦄ (h : A ⟶ A'), W h → HasLiftingProperty ((F.map h).app B) p) :
    HasLiftingProperty ((F.map f₁).app B) p :=
  hasLiftingProperty_right p ((underFunctor F incl hincl B).map f₁) (fun e ↦
    ((D.adj B).hasLiftingProperty_iff _ _).2 (hf₁ _ (fun _ _ h hh ↦
      ((D.adj B).hasLiftingProperty_iff _ _).1 (by
        refine ⟨fun {u v} hsq ↦ ?_⟩
        obtain ⟨l⟩ := ((hW h hh).sq_hasLift (hsq.map (Under.forget B))).exists_lift
        have hl : ((underFunctor F incl hincl B).obj _).hom ≫ l.l = (Under.mk e).hom := by
          rw [← Under.w ((underFunctor F incl hincl B).map h)]
          exact (Category.assoc _ _ _).trans ((congrArg _ l.fac_left).trans (Under.w u))
        exact ⟨⟨⟨Under.homMk l.l hl, Under.UnderMorphism.ext l.fac_left,
          Under.UnderMorphism.ext l.fac_right⟩⟩⟩))))

end UnderAdjoints

end Leibniz

private noncomputable def joinRightUnderAdjoints :
    UnderAdjoints (Functor.curry.obj joinFunctor.{u}) joinInclRight
      (fun f B ↦ (joinInclRight_comp_joinMap f (𝟙 B)).trans (Category.id_comp _)) where
  incl_comp_map X _ _ g := joinInclRight_comp_joinMap (𝟙 X) g
  R := slice
  adj := joinRightUnderAdjunction

private noncomputable def joinLeftUnderAdjoints :
    UnderAdjoints (Functor.curry.obj joinFunctor.{u}).flip (fun Y A ↦ joinInclLeft A Y)
      (fun g A ↦ (joinInclLeft_comp_joinMap (𝟙 A) g).trans (Category.id_comp _)) where
  incl_comp_map Y _ _ g := joinInclLeft_comp_joinMap g (𝟙 Y)
  R := coslice
  adj := joinLeftUnderAdjunction

noncomputable def sliceRes {B B' : SSet.{u}} (g : B' ⟶ B) (t : Under B) :
    (slice B).obj t ⟶ (slice B').obj (Under.mk (g ≫ t.hom)) :=
  joinRightUnderAdjoints.res g t

noncomputable def leibnizSlice {A B E S : SSet.{u}} (j : A ⟶ B) (p : E ⟶ S) (e : B ⟶ E) :
    (slice B).obj (Under.mk e) ⟶ pullback ((slice A).map (Under.homMk p (by simp) :
      Under.mk (j ≫ e) ⟶ Under.mk (j ≫ e ≫ p))) (sliceRes j (Under.mk (e ≫ p))) :=
  joinRightUnderAdjoints.leibnizSlice j p e

@[reassoc]
theorem sliceRes_naturality {B B' : SSet.{u}} (g : B' ⟶ B) {t t' : Under B} (k : t ⟶ t') :
    sliceRes g t ≫ (slice B').map (Under.homMk k.right (by simp [Under.w k]) :
      Under.mk (g ≫ t.hom) ⟶ Under.mk (g ≫ t'.hom)) = (slice B).map k ≫ sliceRes g t' :=
  joinRightUnderAdjoints.res_comp_map g k

theorem sliceRes_comp {A B T : SSet.{u}} (a : A ⟶ B) (b : B ⟶ T) (t : Under T) :
    sliceRes b t ≫ sliceRes a (Under.mk (b ≫ t.hom)) = sliceRes (a ≫ b) t := by
  refine (joinRightUnderAdjoints.res_comp a b t).trans ?_
  have : (Under.homMk (𝟙 _) (by simp) :
      Under.mk ((a ≫ b) ≫ t.hom) ⟶ Under.mk (a ≫ b ≫ t.hom)) = 𝟙 _ := rfl
  rw [this]
  exact (congrArg (_ ≫ ·) ((slice A).map_id _)).trans (Category.comp_id _)

@[reassoc (attr := simp)]
theorem leibnizSlice_fst {A B E S : SSet.{u}} (j : A ⟶ B) (p : E ⟶ S) (e : B ⟶ E) :
    leibnizSlice j p e ≫ pullback.fst _ _ = sliceRes j (Under.mk e) :=
  joinRightUnderAdjoints.leibnizSlice_fst j p e

@[reassoc (attr := simp)]
theorem leibnizSlice_snd {A B E S : SSet.{u}} (j : A ⟶ B) (p : E ⟶ S) (e : B ⟶ E) :
    leibnizSlice j p e ≫ pullback.snd _ _ =
      (slice B).map (Under.homMk p : Under.mk e ⟶ Under.mk (e ≫ p)) :=
  joinRightUnderAdjoints.leibnizSlice_snd j p e

private lemma sliceRes_eq {B B' : SSet.{u}} (g : B' ⟶ B) (t : Under B) :
    sliceRes g t = (joinRightUnderAdjunction B').homEquiv _ (Under.mk (g ≫ t.hom))
      (Under.homMk (joinMap (𝟙 ((slice B).obj t)) g ≫
        (((joinRightUnderAdjunction B).homEquiv _ t).symm (𝟙 _)).right) (by
          exact (joinInclRight_comp_joinMap_assoc _ _ _).trans (congrArg (g ≫ ·)
            (Under.w (((joinRightUnderAdjunction B).homEquiv _ t).symm (𝟙 _)))))) :=
  rfl

@[reassoc (attr := simp)]
theorem sliceRes_sliceπ {B B' : SSet.{u}} (g : B' ⟶ B) (t : Under B) :
    sliceRes g t ≫ sliceπ (Under.mk (g ≫ t.hom)) = sliceπ t := by
  rw [comp_sliceπ, sliceRes_eq, Equiv.symm_apply_apply]
  exact (joinInclLeft_comp_joinMap_assoc (𝟙 _) g _).trans ((Category.id_comp _).trans
    ((comp_sliceπ (𝟙 _)).symm.trans (Category.id_comp _)))

@[reassoc]
theorem leibnizSlice_fst_sliceπ {A B E S : SSet.{u}} (j : A ⟶ B) (p : E ⟶ S) (e : B ⟶ E) :
    leibnizSlice j p e ≫ pullback.fst _ _ ≫ sliceπ (Under.mk (j ≫ e)) = sliceπ (Under.mk e) :=
  (leibnizSlice_fst_assoc _ _ _ _).trans (sliceRes_sliceπ j (Under.mk e))

theorem hasLiftingProperty_leibnizSlice_iff {K L A B E S : SSet.{u}} {i : K ⟶ L} {j : A ⟶ B}
    (sq : (Functor.curry.obj joinFunctor).PushoutObjObj i j) (p : E ⟶ S) (e : B ⟶ E) :
    HasLiftingProperty i (leibnizSlice j p e) ↔
      ∀ {u : sq.pt ⟶ E} {v : join L B ⟶ S} (hsq : CommSq u sq.ι p v),
        joinInclRight K B ≫ sq.inr ≫ u = e → hsq.HasLift :=
  joinRightUnderAdjoints.hasLiftingProperty_leibnizSlice_iff p e sq

section Subcomplex

variable {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex)

private lemma range_joinMap_id_ι :
    Subcomplex.range (joinMap (𝟙 X) B.ι) = (⊤ : X.Subcomplex).join B := by
  have : Epi (joinMap (⊤ : X.Subcomplex).ι (𝟙 (B : SSet.{u}))) :=
    inferInstanceAs (Epi (joinFunctor.mapIso
      ((asIso (⊤ : X.Subcomplex).ι).prod (Iso.refl (B : SSet.{u})))).hom)
  have h : joinMap (⊤ : X.Subcomplex).ι B.ι =
      joinMap (⊤ : X.Subcomplex).ι (𝟙 _) ≫ joinMap (𝟙 X) B.ι :=
    (congrArg₂ (fun f g ↦ joinMap f g) (Category.comp_id _).symm (Category.id_comp _).symm).trans
      (joinFunctor.map_comp (X := (((⊤ : X.Subcomplex) : SSet.{u}), (B : SSet.{u})))
        (Y := (X, (B : SSet.{u}))) (Z := (X, Y)) ((⊤ : X.Subcomplex).ι, 𝟙 _) (𝟙 X, B.ι))
  rw [Subcomplex.join, h, Subcomplex.range_comp, (Subcomplex.range_eq_top_iff _).2 this,
    Subcomplex.image_top]

private lemma range_joinMap_ι_id :
    Subcomplex.range (joinMap A.ι (𝟙 Y)) = A.join (⊤ : Y.Subcomplex) := by
  have : Epi (joinMap (𝟙 (A : SSet.{u})) (⊤ : Y.Subcomplex).ι) :=
    inferInstanceAs (Epi (joinFunctor.mapIso
      ((Iso.refl (A : SSet.{u})).prod (asIso (⊤ : Y.Subcomplex).ι))).hom)
  have h : joinMap A.ι (⊤ : Y.Subcomplex).ι =
      joinMap (𝟙 _) (⊤ : Y.Subcomplex).ι ≫ joinMap A.ι (𝟙 Y) :=
    (congrArg₂ (fun f g ↦ joinMap f g) (Category.id_comp _).symm (Category.comp_id _).symm).trans
      (joinFunctor.map_comp (X := ((A : SSet.{u}), ((⊤ : Y.Subcomplex) : SSet.{u})))
        (Y := ((A : SSet.{u}), Y)) (Z := (X, Y)) (𝟙 _, (⊤ : Y.Subcomplex).ι) (A.ι, 𝟙 Y))
  rw [Subcomplex.join, h, Subcomplex.range_comp, (Subcomplex.range_eq_top_iff _).2 this,
    Subcomplex.image_top]

private noncomputable def joinUnion : (join X Y).Subcomplex :=
  Subcomplex.range (joinMap (𝟙 X) B.ι) ⊔ Subcomplex.range (joinMap A.ι (𝟙 Y))

private lemma isPushout_joinUnion :
    IsPushout (joinMap A.ι (𝟙 (B : SSet.{u}))) (joinMap (𝟙 (A : SSet.{u})) B.ι)
      (Subcomplex.lift (joinMap (𝟙 X) B.ι) (le_sup_left : _ ≤ joinUnion A B))
      (Subcomplex.lift (joinMap A.ι (𝟙 Y)) (le_sup_right : _ ≤ joinUnion A B)) :=
  IsPushout.of_forall_isPushout_app fun n ↦ by
    have m₁ : Mono ((joinMap (𝟙 X) B.ι).app n) :=
      (NatTrans.mono_iff_mono_app (joinMap (𝟙 X) B.ι)).1 (mono_joinMap _ _) n
    have m₂ : Mono ((joinUnion A B).ι.app n) := inferInstance
    refine @Types.isPushout_of_isPullback_of_mono _ _ _ _ _ _ _ _ _ ((joinUnion A B).ι.app n) _ _
      ((isPullback_joinMap A.ι B.ι).flip.app n) rfl rfl m₁ m₂ ?_ (fun x y _ _ h ↦
        (mono_iff_injective _).1
          ((NatTrans.mono_iff_mono_app (joinMap A.ι (𝟙 Y))).1 (mono_joinMap _ _) n) h)
    refine Set.eq_univ_of_forall fun ⟨x, hx⟩ ↦ ?_
    obtain ⟨y, hy⟩ | ⟨y, hy⟩ := hx
    · exact Or.inl ⟨y, Subtype.ext hy⟩
    · exact Or.inr ⟨y, Subtype.ext hy⟩

private noncomputable def joinPushoutObjObj :
    (Functor.curry.obj joinFunctor).PushoutObjObj A.ι B.ι where
  pt := joinUnion A B
  inl := Subcomplex.lift (joinMap (𝟙 X) B.ι) le_sup_left
  inr := Subcomplex.lift (joinMap A.ι (𝟙 Y)) le_sup_right
  isPushout := isPushout_joinUnion A B
  ι := (joinUnion A B).ι

end Subcomplex

private lemma mem_ι_range_iff (W : MorphismProperty SSet.{u}) [W.RespectsIso] {X Y : SSet.{u}}
    (f : X ⟶ Y) [Mono f] : W (Subcomplex.range f).ι ↔ W f :=
  W.arrow_mk_iso_iff (Arrow.isoMk (asIso (Subfunctor.toRange f)).symm (Iso.refl _) (by simp))

private lemma mem_ι_preimage (W : MorphismProperty SSet.{u}) [W.RespectsIso] {X Y : SSet.{u}}
    (e : X ≅ Y) (C : Y.Subcomplex) (h : W C.ι) : W (C.preimage e.hom).ι := by
  have h₁ : C.preimage e.hom = Subcomplex.range (C.ι ≫ e.inv) := by
    rw [← Subcomplex.image_eq_range, ← Subcomplex.image_inv, IsIso.Iso.inv_hom]
  rw [h₁]
  exact (mem_ι_range_iff W _).2 <| (W.arrow_mk_iso_iff (Arrow.isoMk
    (f := Arrow.mk (C.ι ≫ e.inv)) (g := Arrow.mk C.ι) (Iso.refl _) e (by simp))).2 h

private lemma innerAnodyneExtensions_ι_iff {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex)
    (sq : (Functor.curry.obj joinFunctor.{u}).PushoutObjObj A.ι B.ι) :
    innerAnodyneExtensions sq.ι ↔ innerAnodyneExtensions (joinUnion A B).ι :=
  innerAnodyneExtensions.arrow_mk_iso_iff (Arrow.isoMk (f := Arrow.mk sq.ι)
    (g := Arrow.mk (joinPushoutObjObj A B).ι)
    (sq.isPushout.isoIsPushout _ _ (joinPushoutObjObj A B).isPushout) (Iso.refl _)
    (sq.hom_ext
      (by simp only [Arrow.mk_hom, Iso.refl_hom, Category.comp_id,
        IsPushout.inl_isoIsPushout_hom_assoc, Functor.PushoutObjObj.inl_ι])
      (by simp only [Arrow.mk_hom, Iso.refl_hom, Category.comp_id,
        IsPushout.inr_isoIsPushout_hom_assoc, Functor.PushoutObjObj.inr_ι])))

private lemma innerAnodyneExtensions_ι_horn_boundary {m n : ℕ} (k : Fin (m + 2)) (hk : 0 < k)
    (sq : (Functor.curry.obj joinFunctor.{u}).PushoutObjObj Λ[m + 1, k].ι ∂Δ[n].ι) :
    innerAnodyneExtensions sq.ι := by
  refine (innerAnodyneExtensions_ι_iff _ _ sq).2 ?_
  have hU : joinUnion Λ[m + 1, k] ∂Δ[n] =
      (Λ[m + 1 + n + 1, k.castLE (by omega)]).preimage (stdSimplexJoinIso.{u} (m + 1) n).hom := by
    rw [joinUnion, range_joinMap_id_ι, range_joinMap_ι_id, sup_comm, horn_join_sup_join_boundary]
  rw [hU]
  refine mem_ι_preimage _ _ _ (innerAnodyneExtensions.horn_ι ?_ ?_)
  · rw [Fin.lt_def, Fin.val_castLE, Fin.val_zero]
    exact Fin.lt_def.1 hk
  · have := k.isLt
    simp only [Fin.lt_def, Fin.val_castLE, Fin.val_last]
    omega

theorem innerAnodyneExtensions_pushoutObjObjι_join {A₀ A B₀ B : SSet.{u}} {i : A₀ ⟶ A}
    {j : B₀ ⟶ B} (sq : (Functor.curry.obj joinFunctor).PushoutObjObj i j)
    (hi : rightAnodyneExtensions i) [Mono j] : innerAnodyneExtensions sq.ι := by
  intro E S p hp
  refine joinRightUnderAdjoints.hasLiftingProperty_ι_of_llp_rlp p rightHornInclusions hi sq ?_
  rintro _ _ _ ⟨k, hk⟩
  have hj : modelCategoryQuillen.I.rlp.llp j := by
    rw [← rlp_monomorphisms]
    exact le_llp_rlp _ _ (monomorphisms.infer_property j)
  refine joinLeftUnderAdjoints.hasLiftingProperty_ι_of_llp_rlp p _ hj
    (Functor.PushoutObjObj.ofHasPushout _ _ _).flip ?_
  rintro _ _ _ ⟨n⟩
  exact innerAnodyneExtensions_ι_horn_boundary k hk
    (Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj joinFunctor.{u}).flip _ _).flip _ hp

private lemma innerAnodyneExtensions_ι_boundary_horn {m n : ℕ} (k : Fin (n + 2))
    (hk : k < Fin.last (n + 1))
    (sq : (Functor.curry.obj joinFunctor.{u}).PushoutObjObj ∂Δ[m].ι Λ[n + 1, k].ι) :
    innerAnodyneExtensions sq.ι := by
  refine (innerAnodyneExtensions_ι_iff _ _ sq).2 ?_
  have hU : joinUnion ∂Δ[m] Λ[n + 1, k] =
      (Λ[m + (n + 1) + 1, ⟨m + 1 + k, by omega⟩]).preimage
        (stdSimplexJoinIso.{u} m (n + 1)).hom := by
    rw [joinUnion, range_joinMap_id_ι, range_joinMap_ι_id, sup_comm, boundary_join_sup_join_horn]
  rw [hU]
  have hk' : (k : ℕ) < n + 1 := hk
  refine mem_ι_preimage _ _ _ (innerAnodyneExtensions.horn_ι ?_ ?_) <;>
    simp only [Fin.lt_def, Fin.val_zero, Fin.val_last] <;> omega

theorem innerAnodyneExtensions_pushoutObjObjι_join_of_leftAnodyneExtensions
    {A₀ A B₀ B : SSet.{u}} {i : A₀ ⟶ A} {j : B₀ ⟶ B}
    (sq : (Functor.curry.obj joinFunctor).PushoutObjObj i j) [Mono i]
    (hj : leftAnodyneExtensions j) : innerAnodyneExtensions sq.ι := by
  intro E S p hp
  refine joinLeftUnderAdjoints.hasLiftingProperty_ι_of_llp_rlp p leftHornInclusions hj sq.flip ?_
  rintro _ _ _ ⟨k, hk⟩
  have hi : modelCategoryQuillen.I.rlp.llp i := by
    rw [← rlp_monomorphisms]
    exact le_llp_rlp _ _ (monomorphisms.infer_property i)
  refine joinRightUnderAdjoints.hasLiftingProperty_ι_of_llp_rlp p _ hi
    (Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj joinFunctor.{u}).flip _ _).flip ?_
  rintro _ _ _ ⟨n⟩
  exact innerAnodyneExtensions_ι_boundary_horn k hk
    (Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj joinFunctor.{u}) _ _) _ hp

private lemma range_comp_of_epi {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [Epi f] :
    Subcomplex.range (f ≫ g) = Subcomplex.range g := by
  rw [Subcomplex.range_comp, (Subcomplex.range_eq_top_iff f).2 inferInstance,
    Subcomplex.image_top]

private lemma range_joinMap_id_bot_comp (n : ℕ) :
    Subcomplex.range (joinMap (𝟙 Δ[n]) (⊥ : (Δ[0] : SSet.{u}).Subcomplex).ι ≫
      (stdSimplexJoinIso.{u} n 0).hom) = stdSimplex.face {Fin.last (n + 1)}ᶜ := by
  have := isIso_joinInclLeft_of_isEmpty (Δ[n] : SSet.{u}) (⊥ : (Δ[0] : SSet.{u}).Subcomplex)
  rw [← range_comp_of_epi (joinInclLeft _ _), joinInclLeft_comp_joinMap_assoc, Category.id_comp,
    joinInclLeft_comp_stdSimplexJoinIso_hom, Subcomplex.range_eq_ofSimplex, yonedaEquiv_map,
    inl'_eq_δ_last, stdSimplex.face_singleton_compl]

private lemma yonedaEquiv_joinInclLeft_notMem_range (n : ℕ) :
    yonedaEquiv (joinInclLeft (Δ[n] : SSet.{u}) Δ[0]) ∉
      (Subcomplex.range (joinMap ∂Δ[n].ι (𝟙 (Δ[0] : SSet.{u})))).obj (op ⦋n⦌) := by
  rintro ⟨s, hs⟩
  have := isIso_joinInclLeft_of_isEmpty (∂Δ[n] : SSet.{u}) (⊥ : (Δ[0] : SSet.{u}).Subcomplex)
  have hx : (joinMap ∂Δ[n].ι (𝟙 (Δ[0] : SSet.{u}))).app _ s =
      (joinMap (𝟙 _) (⊥ : (Δ[0] : SSet.{u}).Subcomplex).ι).app _
        ((joinInclLeft _ _).app _ (yonedaEquiv (𝟙 (Δ[n] : SSet.{u})))) := by
    rw [hs, ← yonedaEquiv_comp, ← yonedaEquiv_comp, Category.id_comp, joinInclLeft_comp_joinMap,
      Category.id_comp]
  obtain ⟨x, -, hx₁⟩ := Types.exists_of_isPullback
    ((isPullback_joinMap ∂Δ[n].ι (⊥ : (Δ[0] : SSet.{u}).Subcomplex).ι).app _) _ _ hx
  obtain ⟨y, rfl⟩ := ((isIso_iff_bijective ((joinInclLeft (∂Δ[n] : SSet.{u})
    ((⊥ : (Δ[0] : SSet.{u}).Subcomplex) : SSet.{u})).app (op ⦋n⦌))).1 inferInstance).2 x
  have hy := (ConcreteCategory.congr_hom (NatTrans.congr_app (joinInclLeft_comp_joinMap ∂Δ[n].ι
    (𝟙 ((⊥ : (Δ[0] : SSet.{u}).Subcomplex) : SSet.{u}))) (op ⦋n⦌)) y).symm.trans hx₁
  have hy' := (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1
    (mono_joinInclLeft (Δ[n] : SSet.{u}) ((⊥ : (Δ[0] : SSet.{u}).Subcomplex) : SSet.{u}))
    (op ⦋n⦌)) hy
  have hy'' : y.1 = stdSimplex.objMk (m := op ⦋n⦌) .id := hy'
  exact stdSimplex.notMem_boundary n (hy'' ▸ y.2)

theorem range_joinMap_boundary_comp (n : ℕ) :
    Subcomplex.range (joinMap ∂Δ[n].ι (𝟙 (Δ[0] : SSet.{u})) ≫
      (stdSimplexJoinIso.{u} n 0).hom) = Λ[n + 1, Fin.last (n + 1)] := by
  have hsup : Subcomplex.range (joinMap ∂Δ[n].ι (𝟙 (Δ[0] : SSet.{u})) ≫
      (stdSimplexJoinIso.{u} n 0).hom) ⊔ stdSimplex.face {Fin.last (n + 1)}ᶜ = ∂Δ[n + 1] := by
    have h := boundary_join_sup_join_boundary.{u} n 0
    rw [boundary_zero, ← range_joinMap_ι_id, ← range_joinMap_id_ι] at h
    rw [← range_joinMap_id_bot_comp, Subcomplex.range_comp, Subcomplex.range_comp,
      ← Subcomplex.preimage_inv, ← Subcomplex.preimage_inv, ← Subcomplex.preimage_max, h,
      ← Subcomplex.preimage_comp, IsIso.inv_hom_id, Subcomplex.preimage_id]
  have hσ : stdSimplex.objEquiv.symm (SimplexCategory.δ (Fin.last (n + 1))) ∉
      (Subcomplex.range (joinMap ∂Δ[n].ι (𝟙 (Δ[0] : SSet.{u})) ≫
        (stdSimplexJoinIso.{u} n 0).hom)).obj (op ⦋n⦌) := by
    rintro ⟨s, hs⟩
    refine yonedaEquiv_joinInclLeft_notMem_range n ⟨s, ((isIso_iff_bijective
      ((stdSimplexJoinIso.{u} n 0).hom.app (op ⦋n⦌))).1 inferInstance).1 ?_⟩
    refine (ConcreteCategory.congr_hom (NatTrans.comp_app (joinMap ∂Δ[n].ι (𝟙 (Δ[0] : SSet.{u})))
      (stdSimplexJoinIso.{u} n 0).hom (op ⦋n⦌)) s).symm.trans (hs.trans ?_)
    rw [← yonedaEquiv_comp, joinInclLeft_comp_stdSimplexJoinIso_hom, yonedaEquiv_map,
      inl'_eq_δ_last]
  refine le_antisymm ((subcomplex_le_horn_iff _ _).2 fun h ↦ hσ ?_) ?_
  · rwa [stdSimplex.face_singleton_compl, Subcomplex.ofSimplex_le_iff] at h
  · rw [horn_eq_iSup]
    refine iSup_le fun ⟨j, hj⟩ ↦ ?_
    have hb := face_singleton_compl_le_boundary.{u} j
    rw [← hsup, stdSimplex.face_singleton_compl, Subcomplex.ofSimplex_le_iff] at hb
    rw [stdSimplex.face_singleton_compl, Subcomplex.ofSimplex_le_iff]
    refine hb.resolve_right fun hF ↦ hj ?_
    rw [← Subcomplex.ofSimplex_le_iff, ← stdSimplex.face_singleton_compl,
      stdSimplex.face_le_face_iff, Finset.compl_subset_compl, Finset.singleton_subset_iff,
      Finset.mem_singleton] at hF
    exact Set.mem_singleton_iff.2 hF.symm

private lemma rightAnodyneExtensions_joinMap_boundary (n : ℕ) :
    rightAnodyneExtensions (joinMap ∂Δ[n].ι (𝟙 (Δ[0] : SSet.{u}))) := by
  refine (rightAnodyneExtensions.arrow_mk_iso_iff (Arrow.isoMk
    (f := Arrow.mk (joinMap ∂Δ[n].ι (𝟙 (Δ[0] : SSet.{u}))))
    (g := Arrow.mk (joinMap ∂Δ[n].ι (𝟙 (Δ[0] : SSet.{u})) ≫ (stdSimplexJoinIso.{u} n 0).hom))
    (Iso.refl _) (stdSimplexJoinIso.{u} n 0) (by simp))).2 ?_
  refine (mem_ι_range_iff rightAnodyneExtensions _).1 ?_
  rw [range_joinMap_boundary_comp]
  exact rightAnodyneExtensions.horn_ι (Fin.last_pos' (n := n + 1))

theorem rightAnodyneExtensions_joinMap_id {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    rightAnodyneExtensions (joinMap i (𝟙 Δ[0])) := by
  intro E S p hp
  have hi : modelCategoryQuillen.I.rlp.llp i := by
    rw [← rlp_monomorphisms]
    exact le_llp_rlp _ _ (monomorphisms.infer_property i)
  refine joinRightUnderAdjoints.hasLiftingProperty_map_app_of_llp_rlp p _ Δ[0] hi ?_
  rintro _ _ _ ⟨n⟩
  exact rightAnodyneExtensions_joinMap_boundary n _ hp

theorem rightAnodyneExtensions_joinInclRight (Z : SSet.{u}) :
    rightAnodyneExtensions (joinInclRight Z Δ[0]) := by
  have := isIso_joinInclRight_of_isEmpty ((⊥ : Z.Subcomplex) : SSet.{u}) Δ[0]
  refine (rightAnodyneExtensions.arrow_mk_iso_iff (Arrow.isoMk
    (f := Arrow.mk (joinMap (⊥ : Z.Subcomplex).ι (𝟙 Δ[0]))) (g := Arrow.mk (joinInclRight Z Δ[0]))
    (asIso (joinInclRight _ Δ[0])).symm (Iso.refl _) ?_)).1 (rightAnodyneExtensions_joinMap_id _)
  rw [Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq]
  simp only [Arrow.mk_hom, Iso.refl_hom, Category.comp_id]
  exact ((joinInclRight_comp_joinMap (⊥ : Z.Subcomplex).ι (𝟙 Δ[0])).trans
    (Category.id_comp _)).symm

section JoyalLifting

theorem rightFibrations_leibnizSlice {S T E B : SSet.{u}} (j : S ⟶ T) [Mono j]
    (p : E ⟶ B) [InnerFibration p] (e : T ⟶ E) :
    rightFibrations (leibnizSlice j p e) := by
  rintro _ _ _ ⟨i, h0⟩
  exact joinRightUnderAdjoints.hasLiftingProperty_leibnizSlice p e
    (Functor.PushoutObjObj.ofHasPushout _ _ j)
    (innerAnodyneExtensions_pushoutObjObjι_join _ (rightAnodyneExtensions.horn_ι h0) _
      (mem_innerFibrations p))

theorem trivialFibration_leibnizSlice {A B E S : SSet.{u}} {j : A ⟶ B}
    (hj : leftAnodyneExtensions j) (p : E ⟶ S) [InnerFibration p] (e : B ⟶ E) :
    modelCategoryQuillen.I.rlp (leibnizSlice j p e) := by
  rintro _ _ _ ⟨n⟩
  exact joinRightUnderAdjoints.hasLiftingProperty_leibnizSlice p e
    (Functor.PushoutObjObj.ofHasPushout _ _ j)
    (innerAnodyneExtensions_pushoutObjObjι_join_of_leftAnodyneExtensions _ hj _
      (mem_innerFibrations p))

noncomputable def isTerminalSlice {B Z : SSet.{u}} (hZ : IsTerminal Z) (x : B ⟶ Z) :
    IsTerminal ((slice B).obj (Under.mk x)) :=
  have := (joinRightUnderAdjunction B).rightAdjoint_preservesLimits
  IsTerminal.isTerminalObj (slice B) _ (IsTerminal.ofUniqueHom
    (fun t ↦ Under.homMk (hZ.from t.right) (hZ.hom_ext _ _))
    (fun _ _ ↦ Under.UnderMorphism.ext (hZ.hom_ext _ _)))

theorem rightFibrations_sliceRes {S' S Z : SSet.{u}} [Z.Quasicategory] (g : S' ⟶ S) [Mono g]
    (e : S ⟶ Z) : rightFibrations (sliceRes g (Under.mk e)) := by
  have : IsIso (sliceRes g (Under.mk (e ≫ terminal.from Z))) :=
    isIso_of_isTerminal (isTerminalSlice terminalIsTerminal _)
      (isTerminalSlice terminalIsTerminal _) _
  rw [← leibnizSlice_fst g (terminal.from Z) e]
  exact rightHornInclusions.rlp.comp_mem _ _ (rightFibrations_leibnizSlice g _ e)
    (rlp_of_isIso _ _)

theorem trivialFibration_sliceRes {S' S Z : SSet.{u}} [Z.Quasicategory] {g : S' ⟶ S}
    (hg : leftAnodyneExtensions g) (e : S ⟶ Z) :
    modelCategoryQuillen.I.rlp (sliceRes g (Under.mk e)) := by
  have : IsIso (sliceRes g (Under.mk (e ≫ terminal.from Z))) :=
    isIso_of_isTerminal (isTerminalSlice terminalIsTerminal _)
      (isTerminalSlice terminalIsTerminal _) _
  rw [← leibnizSlice_fst g (terminal.from Z) e]
  exact modelCategoryQuillen.I.rlp.comp_mem _ _ (trivialFibration_leibnizSlice hg _ e)
    (rlp_of_isIso _ _)

theorem hasLift_of_invStruct_join {S T X Y : SSet.{u}} (j : S ⟶ T) [Mono j] (p : X ⟶ Y)
    [InnerFibration p] [X.Quasicategory] [Y.Quasicategory]
    (sq : (Functor.curry.obj joinFunctor).PushoutObjObj Λ[1, 0].ι j) {u : sq.pt ⟶ X}
    {v : join Δ[1] T ⟶ Y} (hsq : CommSq u sq.ι p v)
    (h : Nonempty (Edge.mk' (yonedaEquiv (joinInclLeft Δ[1] S ≫ sq.inl ≫ u))).InvStruct) :
    hsq.HasLift :=
  joinRightUnderAdjoints.hasLift_of_invStruct
    (fun X ↦ @asIso _ _ _ _ (joinInclLeft X ((⊥ : S.Subcomplex) : SSet.{u}))
      (isIso_joinInclLeft_of_isEmpty _ _))
    (fun f ↦ (joinInclLeft_comp_joinMap f (𝟙 _)).symm)
    (fun _ _ ↦ Subcomplex.isInitialBot.hom_ext _ _) (⊥ : S.Subcomplex).ι
    (rightFibrations_leibnizSlice j p) (rightFibrations_sliceRes j)
    (rightFibrations_sliceRes (⊥ : S.Subcomplex).ι) sq hsq
    ⟨h.some.ofEq (congrArg yonedaEquiv
      (joinInclLeft_comp_joinMap_assoc (𝟙 Δ[1]) (⊥ : S.Subcomplex).ι (sq.inl ≫ u)).symm)⟩

end JoyalLifting

private lemma hasLift_horn_zero_aux {X Y : SSet.{u}} (p : X ⟶ Y) [InnerFibration p]
    [X.Quasicategory] [Y.Quasicategory] {n N : ℕ} (hN : 0 + 1 + n + 1 = N)
    {a : (Λ[N, 0] : SSet.{u}) ⟶ X} {b : Δ[N] ⟶ Y} (sq : CommSq a Λ[N, 0].ι p b)
    (hd : (0 : Fin (N + 1)) ≤ 1) (H : ({0, 0, 1} : Finset (Fin (N + 1))).card ≤ N)
    (h : Nonempty (Edge.mk' (a.app _ (horn.edge N 0 0 1 hd H))).InvStruct) : sq.HasLift := by
  subst hN
  let E := stdSimplexJoinIso.{u} (0 + 1) n
  have hU : joinUnion Λ[0 + 1, 0] ∂Δ[n] = (Λ[0 + 1 + n + 1, 0]).preimage E.hom := by
    rw [joinUnion, range_joinMap_id_ι, range_joinMap_ι_id, sup_comm, horn_join_sup_join_boundary]
    rfl
  have h₁ : Subcomplex.range ((joinUnion Λ[0 + 1, 0] ∂Δ[n]).ι ≫ E.hom) ≤ Λ[0 + 1 + n + 1, 0] := by
    rw [← Subcomplex.image_eq_range, Subcomplex.image_le_iff, hU]
  have h₂ : Subcomplex.range (Λ[0 + 1 + n + 1, 0].ι ≫ E.inv) ≤ joinUnion Λ[0 + 1, 0] ∂Δ[n] := by
    rw [← Subcomplex.image_eq_range, Subcomplex.image_le_iff, hU, ← Subcomplex.preimage_comp,
      Iso.inv_hom_id, Subcomplex.preimage_id]
  have hsq : CommSq (Subcomplex.lift _ h₁ ≫ a) (joinPushoutObjObj Λ[0 + 1, 0] ∂Δ[n]).ι p
      (E.hom ≫ b) := ⟨by rw [Category.assoc, sq.w, Subcomplex.lift_ι_assoc]; rfl⟩
  let ι₁ := Subcomplex.lift _ h₁
  let ι₂ := Subcomplex.lift _ h₂
  let f := joinInclLeft Δ[1] ∂Δ[n] ≫ (joinPushoutObjObj Λ[0 + 1, 0] ∂Δ[n]).inl ≫ ι₁
  have e : f ≫ Λ[0 + 1 + n + 1, 0].ι =
      stdSimplex.map (AugmentedSimplexCategory.inl' ⦋0 + 1⦌ ⦋n⦌) :=
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) (Subcomplex.lift_ι _ _))))).trans
      ((joinInclLeft_comp_joinMap_assoc (𝟙 _) ∂Δ[n].ι E.hom).trans
        ((Category.id_comp _).trans (joinInclLeft_comp_stdSimplexJoinIso_hom (0 + 1) n)))
  have hedge : yonedaEquiv f = horn.edge (0 + 1 + n + 1) 0 0 1 hd H := by
    apply Subtype.ext
    refine (yonedaEquiv_comp f Λ[0 + 1 + n + 1, 0].ι).symm.trans ((congrArg yonedaEquiv e).trans ?_)
    rw [yonedaEquiv_map]
    ext i
    fin_cases i
    · exact congrArg Fin.val (AugmentedSimplexCategory.inl'_eval ⦋0 + 1⦌ ⦋n⦌ 0)
    · exact congrArg Fin.val (AugmentedSimplexCategory.inl'_eval ⦋0 + 1⦌ ⦋n⦌ 1)
  obtain ⟨l⟩ := (hasLift_of_invStruct_join ∂Δ[n].ι p (joinPushoutObjObj Λ[0 + 1, 0] ∂Δ[n]) hsq
    ⟨h.some.ofEq ((congrArg (a.app _) hedge.symm).trans ((yonedaEquiv_comp f a).symm.trans
      (congrArg yonedaEquiv ((Category.assoc _ _ _).trans
        (congrArg (_ ≫ ·) (Category.assoc _ _ _))))))⟩).exists_lift
  have hι : ι₂ ≫ ι₁ = 𝟙 _ := (cancel_mono Λ[0 + 1 + n + 1, 0].ι).1 (by
    simp only [ι₁, ι₂, Category.assoc, Subcomplex.lift_ι, Subcomplex.lift_ι_assoc,
      Iso.inv_hom_id, Category.comp_id, Category.id_comp])
  refine ⟨⟨⟨E.inv ≫ l.l, ?_, ?_⟩⟩⟩
  · calc Λ[0 + 1 + n + 1, 0].ι ≫ E.inv ≫ l.l
        = ι₂ ≫ (joinPushoutObjObj Λ[0 + 1, 0] ∂Δ[n]).ι ≫ l.l :=
          ((Category.assoc _ _ _).symm.trans
            (congrArg (· ≫ l.l) (Subcomplex.lift_ι _ h₂).symm)).trans (Category.assoc _ _ _)
      _ = ι₂ ≫ ι₁ ≫ a := congrArg (ι₂ ≫ ·) l.fac_left
      _ = a := by rw [← Category.assoc, hι, Category.id_comp]
  · exact (Category.assoc _ _ _).trans ((congrArg (E.inv ≫ ·) l.fac_right).trans
      (Iso.inv_hom_id_assoc _ _))

theorem hasLift_horn_zero_of_invStruct {X Y : SSet.{u}} (p : X ⟶ Y) [InnerFibration p]
    [X.Quasicategory] [Y.Quasicategory] {n : ℕ} {a : (Λ[n + 2, 0] : SSet.{u}) ⟶ X}
    {b : Δ[n + 2] ⟶ Y} (sq : CommSq a Λ[n + 2, 0].ι p b)
    (h : Nonempty (Edge.mk' (a.app _ (horn.edge (n + 2) 0 0 1 (Fin.zero_le _)
      (by simp)))).InvStruct) : sq.HasLift :=
  hasLift_horn_zero_aux p (n := n) (by omega) sq _ _ h

section Slices

theorem hasLiftingProperty_joinMap_id_iff {K L Z E B : SSet.{u}} (i : K ⟶ L) (p : E ⟶ B) :
    HasLiftingProperty (joinMap i (𝟙 Z)) p ↔ ∀ z : Z ⟶ E,
      HasLiftingProperty i ((slice Z).map (Under.homMk p : Under.mk z ⟶ Under.mk (z ≫ p))) := by
  refine ⟨fun h z ↦ ?_, fun h ↦ UnderAdjoints.hasLiftingProperty_right p
    ((joinRightUnder Z).map i) fun z ↦ ((joinRightUnderAdjunction Z).hasLiftingProperty_iff _ _).2
      (h z)⟩
  rw [← (joinRightUnderAdjunction Z).hasLiftingProperty_iff]
  refine ⟨fun {u v} sq ↦ ?_⟩
  obtain ⟨l⟩ := (h.sq_hasLift (sq.map (Under.forget Z))).exists_lift
  have hl : ((joinRightUnder Z).obj L).hom ≫ l.l = (Under.mk z).hom := by
    rw [← Under.w ((joinRightUnder Z).map i)]
    exact (Category.assoc _ _ _).trans ((congrArg _ l.fac_left).trans (Under.w u))
  exact ⟨⟨⟨Under.homMk l.l hl, Under.UnderMorphism.ext l.fac_left,
    Under.UnderMorphism.ext l.fac_right⟩⟩⟩

private lemma hasLiftingProperty_joinMap_id {K L Z E B : SSet.{u}} {i : K ⟶ L}
    (hi : rightAnodyneExtensions i) (p : E ⟶ B) [InnerFibration p] [HasLiftingProperty i p] :
    HasLiftingProperty (joinMap i (𝟙 Z)) p := by
  let sq := Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj joinFunctor) i
    (⊥ : Z.Subcomplex).ι
  have : HasLiftingProperty sq.ι p :=
    innerAnodyneExtensions_pushoutObjObjι_join sq hi _ (mem_innerFibrations p)
  have : HasLiftingProperty (((Functor.curry.obj joinFunctor).map i).app
      ((⊥ : Z.Subcomplex) : SSet.{u})) p := by
    exact (HasLiftingProperty.iff_of_arrow_iso_left (Arrow.isoMk
      (@asIso _ _ _ _ (joinInclLeft K ((⊥ : Z.Subcomplex) : SSet.{u}))
        (isIso_joinInclLeft_of_isEmpty _ _))
      (@asIso _ _ _ _ (joinInclLeft L ((⊥ : Z.Subcomplex) : SSet.{u}))
        (isIso_joinInclLeft_of_isEmpty _ _))
      (joinInclLeft_comp_joinMap i (𝟙 _))) p).1 inferInstance
  have : HasLiftingProperty sq.inr p := sq.isPushout.flip.hasLiftingProperty p
  change HasLiftingProperty (((Functor.curry.obj joinFunctor).map i).app Z) p
  rw [← sq.inr_ι]
  infer_instance

theorem hasLiftingProperty_slice_map {K L Z E B : SSet.{u}} {i : K ⟶ L}
    (hi : rightAnodyneExtensions i) (p : E ⟶ B) [InnerFibration p] [HasLiftingProperty i p]
    (z : Z ⟶ E) :
    HasLiftingProperty i ((slice Z).map (Under.homMk p : Under.mk z ⟶ Under.mk (z ≫ p))) :=
  (hasLiftingProperty_joinMap_id_iff i p).1 (hasLiftingProperty_joinMap_id hi p) z

instance quasicategory_slice {Z : SSet.{u}} (t : Under Z) [t.right.Quasicategory] :
    ((slice Z).obj t).Quasicategory := by
  refine (quasicategory_iff_of_isTerminal ((slice Z).map (Under.homMk (terminal.from t.right) :
    Under.mk t.hom ⟶ Under.mk (t.hom ≫ terminal.from t.right)))
    (isTerminalSlice terminalIsTerminal _)).2 ⟨?_⟩
  rintro _ _ _ ⟨k, h0, hn⟩
  have : HasLiftingProperty Λ[_ + 2, k].ι (terminal.from t.right) :=
    mem_innerFibrations _ _ (.intro k h0 hn)
  exact hasLiftingProperty_slice_map (rightAnodyneExtensions.horn_ι h0) _ t.hom

end Slices

end SSet
