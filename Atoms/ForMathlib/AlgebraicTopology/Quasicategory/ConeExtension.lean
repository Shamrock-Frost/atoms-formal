import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.CartesianMappingSpace
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.CartesianPrism
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.InvertingHom
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.FatJoin
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.SliceJoin

open CategoryTheory Limits Simplicial Opposite MonoidalCategory MonoidalClosed
  CartesianMonoidalCategory

universe u

namespace SSet

section FiberwiseFinal

variable {E B : SSet.{u}}

private def vertexSubcomplex {X : SSet.{u}} (P : X _⦋0⦌ → Prop) : X.Subcomplex where
  obj n := {σ | ∀ i : Fin (n.unop.len + 1), P (X.map (SimplexCategory.const ⦋0⦌ n.unop i).op σ)}
  map {n m} θ σ hσ i := by
    have h := hσ (θ.unop.toOrderHom i)
    rwa [← SimplexCategory.const_comp, op_comp, Functor.map_comp_apply] at h

private lemma mem_vertexSubcomplex_obj_zero_iff {X : SSet.{u}} (P : X _⦋0⦌ → Prop)
    (x : X _⦋0⦌) : x ∈ (vertexSubcomplex P).obj (op ⦋0⦌) ↔ P x := by
  refine ⟨fun h ↦ ?_, fun h i ↦ ?_⟩
  · have h0 := h 0
    rwa [SimplexCategory.hom_zero_zero (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0), op_id,
      Functor.map_id_apply] at h0
  · rwa [SimplexCategory.hom_zero_zero (SimplexCategory.const ⦋0⦌ ⦋0⦌ i), op_id,
      Functor.map_id_apply]

private lemma map_const_yonedaEquiv {X : SSet.{u}} {m : ℕ} (v : Δ[m] ⟶ X) (i : Fin (m + 1)) :
    X.map (SimplexCategory.const ⦋0⦌ ⦋m⦌ i).op (yonedaEquiv v) =
      v.app _ (stdSimplex.obj₀Equiv.symm i) :=
  (NatTrans.naturality_apply v _ _).symm.trans rfl

private lemma range_le_vertexSubcomplex_iff {X : SSet.{u}} (P : X _⦋0⦌ → Prop) {m : ℕ}
    (v : Δ[m] ⟶ X) :
    Subcomplex.range v ≤ vertexSubcomplex P ↔ ∀ i, P (v.app _ (stdSimplex.obj₀Equiv.symm i)) := by
  rw [Subcomplex.range_eq_ofSimplex, Subcomplex.ofSimplex_le_iff]
  exact forall_congr' fun i ↦ by rw [map_const_yonedaEquiv]

def fiberwiseFinalSubcomplex (p : E ⟶ B) : E.Subcomplex :=
  vertexSubcomplex fun e ↦ IsFinal (fiberVertex p e rfl)

def hasFinalFiberSubcomplex (p : E ⟶ B) : B.Subcomplex :=
  vertexSubcomplex fun b ↦ ∃ ω : (pullback p (yonedaEquiv.symm b)) _⦋0⦌, IsFinal ω

theorem mem_fiberwiseFinalSubcomplex_obj_zero_iff (p : E ⟶ B) (e : E _⦋0⦌) {b : B _⦋0⦌}
    (h : p.app _ e = b) :
    e ∈ (fiberwiseFinalSubcomplex p).obj (op ⦋0⦌) ↔ IsFinal (fiberVertex p e h) := by
  subst h
  exact mem_vertexSubcomplex_obj_zero_iff _ e

theorem mem_hasFinalFiberSubcomplex_obj_zero_iff (p : E ⟶ B) (b : B _⦋0⦌) :
    b ∈ (hasFinalFiberSubcomplex p).obj (op ⦋0⦌) ↔
      ∃ ω : (pullback p (yonedaEquiv.symm b)) _⦋0⦌, IsFinal ω :=
  mem_vertexSubcomplex_obj_zero_iff _ b

theorem range_le_fiberwiseFinalSubcomplex_iff (p : E ⟶ B) {m : ℕ} (v : Δ[m] ⟶ E) :
    Subcomplex.range v ≤ fiberwiseFinalSubcomplex p ↔
      ∀ i, v.app _ (stdSimplex.obj₀Equiv.symm i) ∈ (fiberwiseFinalSubcomplex p).obj (op ⦋0⦌) :=
  (range_le_vertexSubcomplex_iff _ v).trans
    (forall_congr' fun _ ↦ (mem_fiberwiseFinalSubcomplex_obj_zero_iff p _ rfl).symm)

theorem range_le_hasFinalFiberSubcomplex_iff (p : E ⟶ B) {m : ℕ} (v : Δ[m] ⟶ B) :
    Subcomplex.range v ≤ hasFinalFiberSubcomplex p ↔
      ∀ i, v.app _ (stdSimplex.obj₀Equiv.symm i) ∈ (hasFinalFiberSubcomplex p).obj (op ⦋0⦌) :=
  (range_le_vertexSubcomplex_iff _ v).trans
    (forall_congr' fun _ ↦ (mem_hasFinalFiberSubcomplex_obj_zero_iff p _).symm)

theorem exists_fiberVertex_eq (p : E ⟶ B) {b : B _⦋0⦌}
    (ω : (pullback p (yonedaEquiv.symm b)) _⦋0⦌) :
    ∃ (e : E _⦋0⦌) (h : p.app _ e = b), fiberVertex p e h = ω := by
  have hp : yonedaEquiv.symm ω ≫ pullback.fst _ _ ≫ p = yonedaEquiv.symm b := by
    rw [pullback.condition, ← Category.assoc,
      stdSimplex.isTerminalObj₀.hom_ext (_ ≫ _) (𝟙 _), Category.id_comp]
  refine ⟨(pullback.fst p (yonedaEquiv.symm b)).app _ ω, ?_, yonedaEquiv.symm.injective ?_⟩
  · apply yonedaEquiv.symm.injective
    rw [← yonedaEquiv_symm_comp, ← yonedaEquiv_symm_comp, Category.assoc]
    exact hp
  · refine pullback.hom_ext ?_ (stdSimplex.isTerminalObj₀.hom_ext _ _)
    rw [yonedaEquiv_symm_fiberVertex_fst, yonedaEquiv_symm_comp]

private lemma mem_hasFinalFiberSubcomplex_of_mem (p : E ⟶ B) {e : E _⦋0⦌}
    (he : e ∈ (fiberwiseFinalSubcomplex p).obj (op ⦋0⦌)) :
    p.app _ e ∈ (hasFinalFiberSubcomplex p).obj (op ⦋0⦌) :=
  (mem_hasFinalFiberSubcomplex_obj_zero_iff p _).2
    ⟨_, (mem_fiberwiseFinalSubcomplex_obj_zero_iff p e rfl).1 he⟩

theorem range_le_hasFinalFiberSubcomplex (p : E ⟶ B) :
    Subcomplex.range ((fiberwiseFinalSubcomplex p).ι ≫ p) ≤ hasFinalFiberSubcomplex p := by
  rintro n _ ⟨σ, rfl⟩ i
  refine (mem_hasFinalFiberSubcomplex_obj_zero_iff p _).1 ?_
  have e : B.map (SimplexCategory.const ⦋0⦌ n.unop i).op
      (((fiberwiseFinalSubcomplex p).ι ≫ p).app n σ) =
        p.app _ (E.map (SimplexCategory.const ⦋0⦌ n.unop i).op σ.1) :=
    (NatTrans.naturality_apply p _ σ.1).symm
  rw [e]
  exact mem_hasFinalFiberSubcomplex_of_mem p ((mem_vertexSubcomplex_obj_zero_iff _ _).2 (σ.2 i))

noncomputable def fiberwiseFinalRes (p : E ⟶ B) :
    (fiberwiseFinalSubcomplex p : SSet.{u}) ⟶ (hasFinalFiberSubcomplex p : SSet.{u}) :=
  Subcomplex.lift ((fiberwiseFinalSubcomplex p).ι ≫ p) (range_le_hasFinalFiberSubcomplex p)

@[reassoc (attr := simp)]
theorem fiberwiseFinalRes_ι (p : E ⟶ B) :
    fiberwiseFinalRes p ≫ (hasFinalFiberSubcomplex p).ι = (fiberwiseFinalSubcomplex p).ι ≫ p :=
  Subcomplex.lift_ι _ _

end FiberwiseFinal

section Collapse

private lemma stdSimplex_hom_ext {S : SSet.{u}} {n : ℕ} {f g : S ⟶ Δ[n]}
    (h : ∀ (d : ℕ) (x : S _⦋d⦌) (t : Fin (d + 1)), f.app _ x t = g.app _ x t) : f = g :=
  hom_ext fun ⟨⟨d⟩⟩ ↦ ConcreteCategory.hom_ext _ _ fun x ↦ stdSimplex.ext _ _ (h d x)

private def squareCollapseFun : Fin 2 × Fin 2 →o Fin 3 where
  toFun x := if x.1 = 0 then 0 else x.2.succ
  monotone' x y h := by
    obtain ⟨h₁, h₂⟩ := h
    dsimp only
    split_ifs with hx hy hy
    · exact le_rfl
    · exact Fin.zero_le _
    · exact absurd (Fin.le_zero_iff.1 (hy ▸ h₁)) hx
    · exact Fin.succ_le_succ_iff.2 h₂

private noncomputable def squareCollapse : Δ[1] ⊗ Δ[1] ⟶ (Δ[2] : SSet.{u}) :=
  (prodStdSimplex.isoNerve 1 1).hom ≫
    nerveMap (ULift.orderIso.symm.monotone.comp (squareCollapseFun.monotone.comp
      ULift.orderIso.monotone)).functor ≫ (stdSimplex.isoNerve 2).inv

private lemma squareCollapse_app_apply {d : ℕ} (x : (Δ[1] ⊗ Δ[1] : SSet.{u}) _⦋d⦌)
    (t : Fin (d + 1)) : squareCollapse.{u}.app _ x t = if x.1 t = 0 then 0 else (x.2 t).succ :=
  rfl

private lemma lift_δ_one_squareCollapse {Z : SSet.{u}} (z : Z ⟶ Δ[0]) (s : Z ⟶ Δ[1]) :
    lift (z ≫ stdSimplex.δ 1) s ≫ squareCollapse = z ≫ stdSimplex.δ 1 ≫ stdSimplex.δ 2 :=
  stdSimplex_hom_ext fun d x t ↦ by
    rw [NatTrans.comp_app, types_comp_apply, squareCollapse_app_apply, if_pos]
    · exact ((by decide : ∀ i : Fin 1, Fin.succAbove 2 (Fin.succAbove 1 i) = 0) _).symm
    · exact (by decide : ∀ i : Fin 1, Fin.succAbove 1 i = 0) _

private lemma lift_δ_zero_squareCollapse {Z : SSet.{u}} (z : Z ⟶ Δ[0]) (s : Z ⟶ Δ[1]) :
    lift (z ≫ stdSimplex.δ 0) s ≫ squareCollapse = s ≫ stdSimplex.δ 0 :=
  stdSimplex_hom_ext fun d x t ↦ by
    rw [NatTrans.comp_app, types_comp_apply, squareCollapse_app_apply, if_neg]
    · rfl
    · exact (by decide : ∀ i : Fin 1, Fin.succAbove 0 i ≠ 0) _

private lemma lift_comp_δ_one_squareCollapse {Z : SSet.{u}} (c : Z ⟶ Δ[1]) (z : Z ⟶ Δ[0]) :
    lift c (z ≫ stdSimplex.δ 1) ≫ squareCollapse = c ≫ stdSimplex.δ 2 :=
  stdSimplex_hom_ext fun d x t ↦ by
    rw [NatTrans.comp_app, types_comp_apply, squareCollapse_app_apply]
    have h := (by decide : ∀ (i : Fin 2) (j : Fin 1),
      (if i = 0 then 0 else (Fin.succAbove 1 j).succ) = Fin.succAbove 2 i)
    exact h _ _

private lemma squareCollapse_σ_one :
    squareCollapse.{u} ≫ stdSimplex.σ 1 = fst _ _ :=
  stdSimplex_hom_ext fun d x t ↦ by
    rw [NatTrans.comp_app, types_comp_apply]
    have h := (by decide : ∀ (i j : Fin 2),
      Fin.predAbove 1 (if i = 0 then 0 else j.succ) = i)
    exact h _ _

private def contractToLastFun (n : ℕ) : Fin 2 × Fin (n + 1) →o Fin (n + 1) where
  toFun x := if x.1 = 0 then x.2 else Fin.last n
  monotone' x y h := by
    obtain ⟨h₁, h₂⟩ := h
    dsimp only
    split_ifs with hx hy hy
    · exact h₂
    · exact Fin.le_last _
    · exact absurd (Fin.le_zero_iff.1 (hy ▸ h₁)) hx
    · exact le_rfl

noncomputable def contractToLast (n : ℕ) : Δ[1] ⊗ Δ[n] ⟶ (Δ[n] : SSet.{u}) :=
  (prodStdSimplex.isoNerve 1 n).hom ≫
    nerveMap (ULift.orderIso.symm.monotone.comp ((contractToLastFun n).monotone.comp
      ULift.orderIso.monotone)).functor ≫ (stdSimplex.isoNerve n).inv

private lemma contractToLast_app_apply {n d : ℕ} (x : (Δ[1] ⊗ Δ[n] : SSet.{u}) _⦋d⦌)
    (t : Fin (d + 1)) :
    (contractToLast.{u} n).app _ x t = if x.1 t = 0 then x.2 t else Fin.last n := rfl

@[reassoc]
theorem lift_δ_one_contractToLast {n : ℕ} {Z : SSet.{u}} (z : Z ⟶ Δ[0]) (v : Z ⟶ Δ[n]) :
    lift (z ≫ stdSimplex.δ 1) v ≫ contractToLast n = v :=
  stdSimplex_hom_ext fun d x t ↦ by
    rw [NatTrans.comp_app, types_comp_apply, contractToLast_app_apply, if_pos]
    · rfl
    · exact (by decide : ∀ i : Fin 1, Fin.succAbove 1 i = 0) _

@[reassoc]
theorem lift_δ_zero_contractToLast {n : ℕ} {Z : SSet.{u}} (z : Z ⟶ Δ[0]) (v : Z ⟶ Δ[n]) :
    lift (z ≫ stdSimplex.δ 0) v ≫ contractToLast n =
      z ≫ yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (Fin.last n)) :=
  stdSimplex_hom_ext fun d x t ↦ by
    rw [NatTrans.comp_app, types_comp_apply, contractToLast_app_apply, if_neg]
    · rfl
    · exact (by decide : ∀ i : Fin 1, Fin.succAbove 0 i ≠ 0) _

@[reassoc]
theorem lift_last_contractToLast {n : ℕ} {Z : SSet.{u}} (c : Z ⟶ Δ[1]) (z : Z ⟶ Δ[0]) :
    lift c (z ≫ yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (Fin.last n))) ≫
      contractToLast n = z ≫ yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (Fin.last n)) :=
  stdSimplex_hom_ext fun d x t ↦ by
    rw [NatTrans.comp_app, types_comp_apply, contractToLast_app_apply]
    split_ifs <;> rfl

theorem lastVertex_ι {n : ℕ} :
    yonedaEquiv.symm (boundary.lastVertex.{u} n) ≫ (∂Δ[n + 1]).ι =
      yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (Fin.last (n + 1))) := by
  rw [yonedaEquiv_symm_comp]
  rfl

theorem prismLastEdge_eq (n : ℕ) :
    prismLastEdge.{u} n = lift (𝟙 Δ[1]) (stdSimplex.isTerminalObj₀.from _ ≫
      yonedaEquiv.symm (boundary.lastVertex n)) ≫ Subcomplex.unionProd.ι₁ _ _ := by
  rw [← cancel_mono (Subcomplex.unionProd _ _).ι, prismLastEdge, Subcomplex.lift_ι,
    Category.assoc, Subcomplex.unionProd.ι₁_ι, lift_whiskerLeft, Category.assoc, lastVertex_ι]
  exact congrArg _ (stdSimplex_hom_ext fun _ _ _ ↦ rfl)

end Collapse

private lemma mono_whiskerRight {Y Z : SSet.{u}} (f : Y ⟶ Z) [Mono f] (W : SSet.{u}) :
    Mono (f ▷ W) :=
  ⟨fun a b h ↦ CartesianMonoidalCategory.hom_ext _ _
    ((cancel_mono f).1 (by simpa using congrArg (· ≫ fst _ _) h))
    (by simpa using congrArg (· ≫ snd _ _) h)⟩

instance mono_fatJoinInclRight (X Y : SSet.{u}) : Mono (fatJoinInclRight X Y) := by
  have := mono_whiskerRight (∂Δ[1]).ι (X ⊗ Y)
  have : Mono (fatJoinIncl X Y) :=
    (MorphismProperty.monomorphisms SSet.{u}).of_isPushout (isPushout_fatJoin X Y) this
  exact mono_comp coprod.inr _

section FatCone

variable {K X : SSet.{u}} {n : ℕ}
  (f₀ : (∂Δ[n + 1] : SSet.{u}) ⟶ (ihom (fatJoin Δ[0] K)).obj X) (g : Δ[n + 1] ⟶ (ihom K).obj X)
  (hfg : (∂Δ[n + 1]).ι ≫ g = f₀ ≫ (pre (fatJoinInclRight Δ[0] K)).app X)

@[reassoc]
private lemma comp_eq_from {Y Z : SSet.{u}} (f : Z ⟶ Y) (h : Y ⟶ Δ[0]) :
    f ≫ h = stdSimplex.isTerminalObj₀.from Z :=
  stdSimplex.isTerminalObj₀.hom_ext _ _

private lemma whiskerLeft_eq_lift (Y : SSet.{u}) {Z Z' : SSet.{u}} (f : Z ⟶ Z') :
    Y ◁ f = lift (fst _ _) (snd _ _ ≫ f) := by
  ext <;> simp

private lemma whiskerRight_eq_lift {Z Z' : SSet.{u}} (f : Z ⟶ Z') (Y : SSet.{u}) :
    f ▷ Y = lift (fst _ _ ≫ f) (snd _ _) := by
  ext <;> simp

private lemma lift_comp_uncurry {A Y Y' Z : SSet.{u}} (P : Z ⟶ A) (v : Z ⟶ Y') (t : Y' ⟶ Y)
    (f : Y ⟶ (ihom A).obj X) : lift P (v ≫ t) ≫ uncurry f = lift P v ≫ uncurry (t ≫ f) := by
  rw [uncurry_natural_left, lift_whiskerLeft_assoc]

private lemma pre_app_comp {A A' A'' : SSet.{u}} (i : A ⟶ A') (j : A' ⟶ A'') :
    (pre j).app X ≫ (pre i).app X = (pre (i ≫ j)).app X := by
  rw [pre_map, NatTrans.comp_app]

@[reassoc]
private lemma lift_δ_zero_fatJoinCyl {Z : SSet.{u}} (z : Z ⟶ Δ[0]) (w : Z ⟶ Δ[0] ⊗ K) :
    lift (z ≫ stdSimplex.δ 0) w ≫ fatJoinCyl Δ[0] K = w ≫ snd _ _ ≫ fatJoinInclRight Δ[0] K := by
  rw [← lift_whiskerRight_assoc, stdSimplex_δ_zero_whiskerRight_fatJoinCyl, lift_snd_assoc]

@[reassoc]
private lemma lift_δ_one_fatJoinCyl {Z : SSet.{u}} (z : Z ⟶ Δ[0]) (w : Z ⟶ Δ[0] ⊗ K) :
    lift (z ≫ stdSimplex.δ 1) w ≫ fatJoinCyl Δ[0] K = w ≫ fst _ _ ≫ fatJoinInclLeft Δ[0] K := by
  rw [← lift_whiskerRight_assoc, stdSimplex_δ_one_whiskerRight_fatJoinCyl, lift_snd_assoc]

private noncomputable def coneEdge₀₁ :
    Δ[1] ⟶ (ihom ((∂Δ[n + 1] : SSet.{u}) ⊗ (Δ[0] ⊗ K))).obj X :=
  curry (lift (fst _ _ ≫ fst _ _) (lift (snd _ _) (fst _ _ ≫ snd _ _)) ≫
    uncurry (fatJoinCyl Δ[0] K ≫ ihomSwap _ _ X f₀))

private noncomputable def coneEdge₁₂ :
    Δ[1] ⟶ (ihom ((∂Δ[n + 1] : SSet.{u}) ⊗ (Δ[0] ⊗ K))).obj X :=
  curry (lift (lift (snd _ _) (fst _ _ ≫ fst _ _ ≫ (∂Δ[n + 1]).ι) ≫ contractToLast (n + 1))
    (fst _ _ ≫ snd _ _ ≫ snd _ _) ≫ uncurry (ihomSwap _ _ X g))

include hfg in
@[reassoc]
private lemma inclRight_ihomSwap :
    fatJoinInclRight Δ[0] K ≫ ihomSwap _ _ X f₀ =
      ihomSwap _ _ X g ≫ (pre (∂Δ[n + 1]).ι).app X := by
  rw [← ihomSwap_comp_pre_app, ← hfg, ihomSwap_comp]

include hfg in
private lemma lift_inclRight_uncurry_ihomSwap {Z : SSet.{u}} (a : Z ⟶ ∂Δ[n + 1])
    (w : Z ⟶ Δ[0] ⊗ K) :
    lift a (w ≫ snd _ _ ≫ fatJoinInclRight Δ[0] K) ≫ uncurry (ihomSwap _ _ X f₀) =
      lift (a ≫ (∂Δ[n + 1]).ι) (w ≫ snd _ _) ≫ uncurry (ihomSwap _ _ X g) := by
  rw [← lift_whiskerLeft_assoc, ← uncurry_natural_left, Category.assoc,
    inclRight_ihomSwap f₀ g hfg, uncurry_natural_left, uncurry_pre_app, lift_whiskerLeft_assoc,
    lift_whiskerRight_assoc]

include hfg in
@[reassoc]
private lemma δ_zero_coneEdge₀₁ :
    stdSimplex.δ 0 ≫ coneEdge₀₁ f₀ = stdSimplex.δ 1 ≫ coneEdge₁₂ g := by
  rw [coneEdge₀₁, coneEdge₁₂, ← curry_natural_left, ← curry_natural_left]
  congr 1
  rw [uncurry_natural_left]
  simp only [comp_lift_assoc, whiskerLeft_snd, whiskerLeft_fst_assoc, lift_whiskerLeft_assoc]
  rw [lift_δ_zero_fatJoinCyl, lift_δ_one_contractToLast,
    lift_inclRight_uncurry_ihomSwap f₀ g hfg]
  simp only [Category.assoc]

variable (K X n) in
private noncomputable abbrev coneRes :
    (ihom ((∂Δ[n + 1] : SSet.{u}) ⊗ (Δ[0] ⊗ K))).obj X ⟶ (ihom (Δ[0] ⊗ (Δ[0] ⊗ K))).obj X :=
  (pre (yonedaEquiv.symm (boundary.lastVertex n) ▷ (Δ[0] ⊗ K))).app X

private noncomputable def coneHornTop :
    (Λ[2, 1] : SSet.{u}) ⟶ (ihom ((∂Δ[n + 1] : SSet.{u}) ⊗ (Δ[0] ⊗ K))).obj X :=
  horn₂₁.isPushout.desc (coneEdge₀₁ f₀) (coneEdge₁₂ g) (δ_zero_coneEdge₀₁ f₀ g hfg)

@[reassoc]
private lemma δ_two_σ_one :
    stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.σ (1 : Fin 2) = 𝟙 (Δ[1] : SSet.{u}) :=
  CosimplicialObject.δ_comp_σ_succ (X := stdSimplex) (i := 1)

private lemma δ_zero_σ_one :
    stdSimplex.δ (0 : Fin 3) ≫ stdSimplex.σ (1 : Fin 2) =
      stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{u}) ≫ stdSimplex.δ 0 :=
  stdSimplex_hom_ext fun d x t ↦ by
    have h := (by decide : ∀ i : Fin 2, Fin.predAbove 1 (Fin.succAbove 0 i) = Fin.succAbove 0 0)
    exact h _

variable (K X n) in
private lemma hasLiftingProperty_coneRes [X.Quasicategory] :
    HasLiftingProperty (Λ[2, 1] : (Δ[2] : SSet.{u}).Subcomplex).ι (coneRes K X n) :=
  have : Mono (yonedaEquiv.symm (boundary.lastVertex.{u} n)) :=
    stdSimplex.isTerminalObj₀.mono_from _
  have := mono_whiskerRight (yonedaEquiv.symm (boundary.lastVertex.{u} n)) (Δ[0] ⊗ K)
  mem_innerFibrations _ _ (horn_ι_mem_innerHornInclusions (by decide) (by decide))

private lemma coneEdge₁₂_coneRes :
    coneEdge₁₂ g ≫ coneRes K X n = stdSimplex.isTerminalObj₀.from _ ≫ stdSimplex.δ 1 ≫
      coneEdge₁₂ g ≫ coneRes K X n := by
  rw [coneEdge₁₂, curry_pre_app, ← curry_natural_left, ← curry_natural_left]
  congr 1
  simp only [comp_lift_assoc, whiskerLeft_fst_assoc, whiskerRight_snd, whiskerRight_snd_assoc,
    whiskerRight_fst_assoc, comp_eq_from_assoc, lastVertex_ι, lift_last_contractToLast]

private lemma coneHornTop_commSq :
    CommSq (coneHornTop f₀ g hfg) (Λ[2, 1] : (Δ[2] : SSet.{u}).Subcomplex).ι (coneRes K X n)
      (stdSimplex.σ 1 ≫ coneEdge₀₁ f₀ ≫ coneRes K X n) := by
  refine ⟨horn₂₁.isPushout.hom_ext ?_ ?_⟩
  · rw [coneHornTop, IsPushout.inl_desc_assoc, ← Category.assoc horn₂₁.ι₀₁,
      (by simp : horn₂₁.ι₀₁ ≫ (Λ[2, 1] : (Δ[2] : SSet.{u}).Subcomplex).ι = stdSimplex.δ 2),
      δ_two_σ_one_assoc]
  · rw [coneHornTop, IsPushout.inr_desc_assoc, ← Category.assoc horn₂₁.ι₁₂,
      (by simp : horn₂₁.ι₁₂ ≫ (Λ[2, 1] : (Δ[2] : SSet.{u}).Subcomplex).ι = stdSimplex.δ 0),
      reassoc_of% δ_zero_σ_one, δ_zero_coneEdge₀₁_assoc f₀ g hfg, ← coneEdge₁₂_coneRes]

private noncomputable def coneTriangle [X.Quasicategory] :
    Δ[2] ⟶ (ihom ((∂Δ[n + 1] : SSet.{u}) ⊗ (Δ[0] ⊗ K))).obj X :=
  have := hasLiftingProperty_coneRes K X n
  (coneHornTop_commSq f₀ g hfg).lift

private lemma δ_two_coneTriangle [X.Quasicategory] :
    stdSimplex.δ 2 ≫ coneTriangle f₀ g hfg = coneEdge₀₁ f₀ := by
  have := hasLiftingProperty_coneRes K X n
  rw [← (by simp : horn₂₁.ι₀₁ ≫ (Λ[2, 1] : (Δ[2] : SSet.{u}).Subcomplex).ι = stdSimplex.δ 2),
    Category.assoc, coneTriangle, CommSq.fac_left, coneHornTop, IsPushout.inl_desc]

private lemma δ_zero_coneTriangle [X.Quasicategory] :
    stdSimplex.δ 0 ≫ coneTriangle f₀ g hfg = coneEdge₁₂ g := by
  have := hasLiftingProperty_coneRes K X n
  rw [← (by simp : horn₂₁.ι₁₂ ≫ (Λ[2, 1] : (Δ[2] : SSet.{u}).Subcomplex).ι = stdSimplex.δ 0),
    Category.assoc, coneTriangle, CommSq.fac_left, coneHornTop, IsPushout.inr_desc]

private lemma coneTriangle_coneRes [X.Quasicategory] :
    coneTriangle f₀ g hfg ≫ coneRes K X n = stdSimplex.σ 1 ≫ coneEdge₀₁ f₀ ≫ coneRes K X n := by
  have := hasLiftingProperty_coneRes K X n
  rw [coneTriangle, CommSq.fac_right]

private noncomputable def coneCyl [X.Quasicategory] :
    Δ[1] ⊗ (Δ[0] ⊗ K) ⟶ (ihom (Δ[1] ⊗ (∂Δ[n + 1] : SSet.{u}))).obj X :=
  curry (lift (lift (fst _ _ ≫ snd _ _) (snd _ _ ≫ snd _ _))
    (lift (snd _ _ ≫ fst _ _) (fst _ _ ≫ fst _ _) ≫ squareCollapse) ≫
    uncurry (coneTriangle f₀ g hfg))

private lemma δ_one_coneCyl [X.Quasicategory] :
    stdSimplex.δ 1 ▷ (Δ[0] ⊗ K) ≫ coneCyl f₀ g hfg = snd _ _ ≫ fst _ _ ≫
      fatJoinInclLeft Δ[0] K ≫ ihomSwap _ _ X f₀ ≫ (pre (snd _ _)).app X := by
  rw [coneCyl, ← curry_natural_left, curry_eq_iff]
  simp only [← Category.assoc, uncurry_pre_app]
  simp only [uncurry_natural_left, whiskerLeft_eq_lift, whiskerRight_eq_lift,
    comp_lift_assoc, comp_lift, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc, Category.assoc,
    comp_eq_from, comp_eq_from_assoc, lift_δ_one_squareCollapse]
  rw [lift_comp_uncurry, Category.assoc, δ_two_coneTriangle, coneEdge₀₁, ← curry_natural_left,
    uncurry_curry]
  simp only [uncurry_natural_left, whiskerLeft_eq_lift, comp_lift_assoc, lift_fst, lift_snd,
    lift_fst_assoc, lift_snd_assoc, Category.assoc, comp_eq_from_assoc, lift_δ_one_fatJoinCyl]

private lemma δ_zero_coneCyl [X.Quasicategory] :
    stdSimplex.δ 0 ▷ (Δ[0] ⊗ K) ≫ coneCyl f₀ g hfg = snd _ _ ≫ snd _ _ ≫
      ihomSwap _ _ X g ≫ (pre (Δ[1] ◁ (∂Δ[n + 1]).ι ≫ contractToLast (n + 1))).app X := by
  rw [coneCyl, ← curry_natural_left, curry_eq_iff]
  simp only [← Category.assoc, uncurry_pre_app]
  simp only [uncurry_natural_left, whiskerLeft_eq_lift, whiskerRight_eq_lift,
    comp_lift_assoc, comp_lift, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc, Category.assoc,
    comp_eq_from_assoc, lift_δ_zero_squareCollapse]
  rw [lift_comp_uncurry, Category.assoc, δ_zero_coneTriangle, uncurry_natural_left, coneEdge₁₂,
    uncurry_curry]
  simp only [whiskerLeft_eq_lift, comp_lift_assoc, lift_snd, lift_fst_assoc, lift_snd_assoc,
    Category.assoc]

private lemma coneCyl_pre_δ_one [X.Quasicategory] :
    coneCyl f₀ g hfg ≫ (pre (stdSimplex.δ 1 ▷ (∂Δ[n + 1] : SSet.{u}))).app X =
      fatJoinCyl Δ[0] K ≫ ihomSwap _ _ X f₀ ≫ (pre (snd _ _)).app X := by
  rw [coneCyl, curry_pre_app, curry_eq_iff]
  simp only [← Category.assoc, uncurry_pre_app]
  simp only [uncurry_natural_left, whiskerLeft_eq_lift, whiskerRight_eq_lift,
    comp_lift_assoc, comp_lift, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc, Category.assoc,
    comp_eq_from_assoc, lift_comp_δ_one_squareCollapse]
  rw [lift_comp_uncurry, Category.assoc, δ_two_coneTriangle, uncurry_natural_left, coneEdge₀₁,
    uncurry_curry]
  simp only [uncurry_natural_left, whiskerLeft_eq_lift, comp_lift_assoc, lift_fst, lift_snd,
    lift_fst_assoc, lift_snd_assoc, lift_comp_fst_snd]

private lemma lift_lastVertex_uncurry {Y Z : SSet.{u}} (z : Z ⟶ Δ[0]) (w : Z ⟶ Δ[0] ⊗ K)
    (t : Z ⟶ Y) (f : Y ⟶ (ihom ((∂Δ[n + 1] : SSet.{u}) ⊗ (Δ[0] ⊗ K))).obj X) :
    lift (lift (z ≫ yonedaEquiv.symm (boundary.lastVertex n)) w) t ≫ uncurry f =
      lift (lift z w) t ≫ uncurry (f ≫ coneRes K X n) := by
  rw [uncurry_pre_app, lift_whiskerRight_assoc, lift_whiskerRight]

private lemma coneCyl_pre_lastVertex [X.Quasicategory] :
    coneCyl f₀ g hfg ≫ (pre (Δ[1] ◁ yonedaEquiv.symm (boundary.lastVertex n))).app X =
      fatJoinCyl Δ[0] K ≫ ihomSwap _ _ X f₀ ≫ (pre (stdSimplex.isTerminalObj₀.from _ ≫
        yonedaEquiv.symm (boundary.lastVertex n))).app X := by
  rw [coneCyl, curry_pre_app, curry_eq_iff]
  simp only [← Category.assoc, uncurry_pre_app]
  simp only [uncurry_natural_left, whiskerLeft_eq_lift, whiskerRight_eq_lift,
    comp_lift_assoc, comp_lift, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc,
    comp_eq_from_assoc]
  rw [lift_lastVertex_uncurry, coneTriangle_coneRes, uncurry_natural_left,
    lift_whiskerLeft_assoc, Category.assoc, squareCollapse_σ_one, lift_fst, uncurry_pre_app,
    coneEdge₀₁, uncurry_curry]
  simp only [uncurry_natural_left, whiskerLeft_eq_lift, whiskerRight_eq_lift,
    comp_lift_assoc, comp_lift, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc,
    comp_eq_from_assoc, lift_comp_fst_snd]

include hfg in
theorem exists_fatCone_homotopy [X.Quasicategory] :
    ∃ H : Δ[1] ⊗ (∂Δ[n + 1] : SSet.{u}) ⟶ (ihom (fatJoin Δ[0] K)).obj X,
      stdSimplex.δ 1 ▷ _ ≫ H = snd _ _ ≫ f₀ ∧
      H ≫ (pre (fatJoinInclRight Δ[0] K)).app X =
        Δ[1] ◁ (∂Δ[n + 1]).ι ≫ contractToLast (n + 1) ≫ g ∧
      Δ[1] ◁ yonedaEquiv.symm (boundary.lastVertex n) ≫ H =
        stdSimplex.isTerminalObj₀.from _ ≫ yonedaEquiv.symm (boundary.lastVertex n) ≫ f₀ := by
  set η := fatJoinDesc (fatJoinInclLeft Δ[0] K ≫ ihomSwap _ _ X f₀ ≫ (pre (snd _ _)).app X)
    (ihomSwap _ _ X g ≫ (pre (Δ[1] ◁ (∂Δ[n + 1]).ι ≫ contractToLast (n + 1))).app X)
    (coneCyl f₀ g hfg) (δ_one_coneCyl f₀ g hfg) (δ_zero_coneCyl f₀ g hfg) with hη
  refine ⟨(ihomSwap _ _ X).symm η, (ihomSwap _ _ X).injective ?_, (ihomSwap _ _ X).injective ?_,
    (ihomSwap _ _ X).injective ?_⟩
  · rw [ihomSwap_comp, ihomSwap_comp, Equiv.apply_symm_apply]
    refine fatJoin_hom_ext ?_ ?_ ?_
    · rw [fatJoinInclLeft_fatJoinDesc_assoc, Category.assoc, Category.assoc, pre_app_comp,
        whiskerRight_snd]
    · rw [fatJoinInclRight_fatJoinDesc_assoc, Category.assoc, pre_app_comp,
        inclRight_ihomSwap_assoc f₀ g hfg, pre_app_comp]
      congr 3
      simp only [whiskerLeft_eq_lift, whiskerRight_eq_lift, comp_lift_assoc, lift_fst,
        lift_snd_assoc, lift_δ_one_contractToLast]
    · rw [fatJoinCyl_fatJoinDesc_assoc, coneCyl_pre_δ_one]
  · rw [ihomSwap_comp_pre_app, Equiv.apply_symm_apply, hη, fatJoinInclRight_fatJoinDesc,
      ← Category.assoc, ihomSwap_comp]
  · rw [ihomSwap_comp, ihomSwap_comp, ihomSwap_comp, Category.assoc, pre_app_comp,
      Equiv.apply_symm_apply]
    refine fatJoin_hom_ext ?_ ?_ ?_
    · rw [fatJoinInclLeft_fatJoinDesc_assoc, Category.assoc, Category.assoc, pre_app_comp,
        whiskerLeft_snd, stdSimplex.isTerminalObj₀.hom_ext (snd _ _)]
    · rw [fatJoinInclRight_fatJoinDesc_assoc, Category.assoc, pre_app_comp,
        inclRight_ihomSwap_assoc f₀ g hfg, pre_app_comp]
      congr 3
      simp only [whiskerLeft_eq_lift, comp_lift_assoc, lift_fst, lift_snd_assoc, lastVertex_ι,
        lift_last_contractToLast, Category.assoc]
      rw [stdSimplex.isTerminalObj₀.hom_ext (snd _ _)]
    · rw [fatJoinCyl_fatJoinDesc_assoc, coneCyl_pre_lastVertex]

end FatCone

section Restriction

lemma subcomplex_ext_of_range {X : SSet.{u}} {S T : X.Subcomplex}
    (h : ∀ (m : ℕ) (v : Δ[m] ⟶ X), Subcomplex.range v ≤ S ↔ Subcomplex.range v ≤ T) :
    S = T := by
  ext ⟨⟨m⟩⟩ σ
  have := h m (yonedaEquiv.symm σ)
  rwa [Subcomplex.range_eq_ofSimplex, Equiv.apply_symm_apply, Subcomplex.ofSimplex_le_iff,
    Subcomplex.ofSimplex_le_iff] at this

lemma fiberMap_app_fiberVertex {E F B : SSet.{u}} {p : E ⟶ B} {q : F ⟶ B} (φ : E ⟶ F)
    (hφ : φ ≫ q = p) (e : E _⦋0⦌) :
    (fiberMap φ hφ (p.app _ e)).app _ (fiberVertex p e rfl) =
      fiberVertex q (φ.app _ e) (by rw [← hφ]; rfl) := by
  apply yonedaEquiv.symm.injective
  refine pullback.hom_ext ?_ (stdSimplex.isTerminalObj₀.hom_ext _ _)
  rw [← yonedaEquiv_symm_comp (fiberVertex p e rfl), Category.assoc,
    ← (isPullback_fiberMap φ hφ _).w,
    yonedaEquiv_symm_fiberVertex_fst_assoc, yonedaEquiv_symm_fiberVertex_fst,
    yonedaEquiv_symm_comp]

lemma pre_app_app_yonedaEquiv {A A' X : SSet.{u}} (i : A ⟶ A') (g : A' ⟶ X) :
    ((pre i).app X).app _ (yonedaEquiv ((ihomPointEquiv A' X).symm g)) =
      yonedaEquiv ((ihomPointEquiv A X).symm (i ≫ g)) := by
  rw [← yonedaEquiv_comp]
  refine congrArg yonedaEquiv ((ihomPointEquiv A X).injective ?_)
  rw [ihomPointEquiv_comp_pre_app, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

end Restriction

section FatConeFibre

variable {K X : SSet.{u}}

private lemma uncurry_ihomPointEquiv_symm (T Z : SSet.{u}) (f : T ⟶ Z) :
    uncurry ((ihomPointEquiv T Z).symm f) = fst T Δ[0] ≫ f := by
  have : fst T Δ[0] ≫ lift (𝟙 T) (stdSimplex.isTerminalObj₀.from T) = 𝟙 _ := by
    ext1
    · simp
    · exact stdSimplex.isTerminalObj₀.hom_ext _ _
  conv_rhs => rw [← Equiv.apply_symm_apply (ihomPointEquiv T Z) f]
  rw [ihomPointEquiv_apply, reassoc_of% this]

private noncomputable def fatConeShuffle (T I K : SSet.{u}) :
    T ⊗ (I ⊗ (Δ[0] ⊗ K)) ≅ I ⊗ (T ⊗ K) where
  hom := lift (snd _ _ ≫ fst _ _) (lift (fst _ _) (snd _ _ ≫ snd _ _ ≫ snd _ _))
  inv := lift (snd _ _ ≫ fst _ _)
    (lift (fst _ _) (lift (stdSimplex.isTerminalObj₀.from _) (snd _ _ ≫ snd _ _)))
  hom_inv_id := by
    ext1
    · simp
    ext1
    · simp
    ext1
    · exact stdSimplex.isTerminalObj₀.hom_ext _ _
    · simp
  inv_hom_id := by ext <;> simp

@[reassoc]
private lemma whiskerLeft_whiskerRight_fatConeShuffle_hom {T I I' : SSet.{u}} (K : SSet.{u})
    (f : I ⟶ I') :
    T ◁ (f ▷ (Δ[0] ⊗ K)) ≫ (fatConeShuffle T I' K).hom =
      (fatConeShuffle T I K).hom ≫ f ▷ (T ⊗ K) := by
  ext <;> simp [fatConeShuffle]

@[reassoc]
private lemma whiskerRight_fatConeShuffle_inv {T I I' : SSet.{u}} (K : SSet.{u}) (f : I ⟶ I') :
    f ▷ (T ⊗ K) ≫ (fatConeShuffle T I' K).inv =
      (fatConeShuffle T I K).inv ≫ T ◁ (f ▷ (Δ[0] ⊗ K)) := by
  rw [← cancel_epi (fatConeShuffle T I K).hom, Iso.hom_inv_id_assoc,
    ← whiskerLeft_whiskerRight_fatConeShuffle_hom_assoc, Iso.hom_inv_id, Category.comp_id]

variable (K) in
private noncomputable def fatConeCollapse (T : SSet.{u}) :
    fatJoin Δ[0] K ⟶ (ihom T).obj (fatJoin T K) :=
  fatJoinDesc ((ihomPointEquiv T _).symm (fatJoinInclLeft T K))
    (fatJoinInclRight T K ≫ constDiagram T _)
    (curry ((fatConeShuffle T Δ[1] K).hom ≫ fatJoinCyl T K))
    (by
      apply uncurry_injective
      rw [uncurry_natural_left, uncurry_curry, whiskerLeft_whiskerRight_fatConeShuffle_hom_assoc,
        stdSimplex_δ_one_whiskerRight_fatJoinCyl, uncurry_natural_left, uncurry_natural_left,
        uncurry_ihomPointEquiv_symm]
      simp [fatConeShuffle])
    (by
      apply uncurry_injective
      rw [uncurry_natural_left, uncurry_curry, whiskerLeft_whiskerRight_fatConeShuffle_hom_assoc,
        stdSimplex_δ_zero_whiskerRight_fatJoinCyl, uncurry_natural_left, uncurry_natural_left,
        uncurry_natural_left, uncurry_constDiagram]
      simp [fatConeShuffle])

private noncomputable def fatConeDesc {T : SSet.{u}} (d : K ⟶ X)
    (g : fatJoin Δ[0] K ⟶ (ihom T).obj X)
    (hg : fatJoinInclRight Δ[0] K ≫ g = d ≫ constDiagram T X) : fatJoin T K ⟶ X :=
  fatJoinDesc (ihomPointEquiv T X (fatJoinInclLeft Δ[0] K ≫ g)) d
    ((fatConeShuffle T Δ[1] K).inv ≫ uncurry (fatJoinCyl Δ[0] K ≫ g))
    (by
      rw [whiskerRight_fatConeShuffle_inv_assoc, ← uncurry_natural_left,
        stdSimplex_δ_one_whiskerRight_fatJoinCyl_assoc, uncurry_natural_left,
        uncurry_natural_left, ihomPointEquiv_apply]
      have : (fatConeShuffle T Δ[0] K).inv ≫ T ◁ snd _ _ ≫ T ◁ fst _ _ =
          snd _ _ ≫ fst _ _ ≫ lift (𝟙 T) (stdSimplex.isTerminalObj₀.from T) := by
        ext1
        · simp [fatConeShuffle]
        · exact stdSimplex.isTerminalObj₀.hom_ext _ _
      simp only [reassoc_of% this])
    (by
      rw [whiskerRight_fatConeShuffle_inv_assoc, ← uncurry_natural_left,
        stdSimplex_δ_zero_whiskerRight_fatJoinCyl_assoc, hg, uncurry_natural_left,
        uncurry_natural_left, uncurry_natural_left, uncurry_constDiagram]
      simp [fatConeShuffle])

@[reassoc]
private lemma fatJoinCyl_fatConeCollapse (T : SSet.{u}) :
    fatJoinCyl Δ[0] K ≫ fatConeCollapse K T =
      curry ((fatConeShuffle T Δ[1] K).hom ≫ fatJoinCyl T K) :=
  fatJoinCyl_fatJoinDesc _ _ _ _ _

private lemma fatJoinInclRight_fatConeCollapse {T : SSet.{u}} (d : K ⟶ X)
    (ψ : fatJoin T K ⟶ X) (hψ : fatJoinInclRight T K ≫ ψ = d) :
    fatJoinInclRight Δ[0] K ≫ fatConeCollapse K T ≫ (ihom T).map ψ = d ≫ constDiagram T X := by
  rw [fatConeCollapse, fatJoinInclRight_fatJoinDesc_assoc, Category.assoc,
    constDiagram_comp_ihom_map, reassoc_of% hψ]

private lemma fatConeDesc_fatConeCollapse {T : SSet.{u}} (d : K ⟶ X) (ψ : fatJoin T K ⟶ X)
    (hψ : fatJoinInclRight T K ≫ ψ = d) :
    fatConeDesc d (fatConeCollapse K T ≫ (ihom T).map ψ)
      (fatJoinInclRight_fatConeCollapse d ψ hψ) = ψ := by
  refine (fatJoin_hom_ext ?_ ?_ ?_).symm
  · rw [fatConeDesc, fatJoinInclLeft_fatJoinDesc, fatConeCollapse,
      fatJoinInclLeft_fatJoinDesc_assoc, ihomPointEquiv_comp_ihom_map, Equiv.apply_symm_apply]
  · rw [fatConeDesc, fatJoinInclRight_fatJoinDesc, hψ]
  · rw [fatConeDesc, fatJoinCyl_fatJoinDesc, fatJoinCyl_fatConeCollapse_assoc,
      uncurry_natural_right, uncurry_curry, Category.assoc, Iso.inv_hom_id_assoc]

private lemma fatConeCollapse_fatConeDesc {T : SSet.{u}} (d : K ⟶ X)
    (g : fatJoin Δ[0] K ⟶ (ihom T).obj X)
    (hg : fatJoinInclRight Δ[0] K ≫ g = d ≫ constDiagram T X) :
    fatConeCollapse K T ≫ (ihom T).map (fatConeDesc d g hg) = g := by
  refine fatJoin_hom_ext ?_ ?_ ?_
  · rw [fatConeCollapse, fatJoinInclLeft_fatJoinDesc_assoc]
    apply (ihomPointEquiv T X).injective
    rw [ihomPointEquiv_comp_ihom_map, Equiv.apply_symm_apply, fatConeDesc,
      fatJoinInclLeft_fatJoinDesc]
  · rw [fatConeCollapse, fatJoinInclRight_fatJoinDesc_assoc, Category.assoc,
      constDiagram_comp_ihom_map, fatConeDesc, fatJoinInclRight_fatJoinDesc_assoc, hg]
  · rw [fatJoinCyl_fatConeCollapse_assoc, ← curry_natural_right, Category.assoc, fatConeDesc,
      fatJoinCyl_fatJoinDesc, Iso.hom_inv_id_assoc, curry_uncurry]

private noncomputable def fatConeEquiv (T : SSet.{u}) (d : K ⟶ X) :
    {g : fatJoin Δ[0] K ⟶ (ihom T).obj X //
        fatJoinInclRight Δ[0] K ≫ g = d ≫ constDiagram T X} ≃
      {ψ : fatJoin T K ⟶ X // fatJoinInclRight T K ≫ ψ = d} where
  toFun g := ⟨fatConeDesc d g.1 g.2, fatJoinInclRight_fatJoinDesc _ _ _ _ _⟩
  invFun ψ := ⟨fatConeCollapse K T ≫ (ihom T).map ψ.1,
    fatJoinInclRight_fatConeCollapse d ψ.1 ψ.2⟩
  left_inv g := Subtype.ext (fatConeCollapse_fatConeDesc d g.1 g.2)
  right_inv ψ := Subtype.ext (fatConeDesc_fatConeCollapse d ψ.1 ψ.2)

private lemma ihomSwap_from_comp (T : SSet.{u}) (w : Δ[0] ⟶ (ihom K).obj X) :
    ihomSwap T K X (stdSimplex.isTerminalObj₀.from T ≫ w) =
      ihomPointEquiv K X w ≫ constDiagram T X := by
  rw [ihomSwap_apply, curry_eq_iff, uncurry_natural_left (ihomPointEquiv K X w),
    uncurry_constDiagram, whiskerLeft_snd, uncurry_natural_left, ihomPointEquiv_apply]
  have : K ◁ stdSimplex.isTerminalObj₀.from T =
      fst K T ≫ lift (𝟙 K) (stdSimplex.isTerminalObj₀.from K) := by
    ext1
    · simp
    · exact stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [reassoc_of% this, braiding_hom_fst_assoc]

private noncomputable def fatConeFiberHomEquiv (T : SSet.{u}) (d : K ⟶ X)
    {b : ((ihom K).obj X) _⦋0⦌} (hb : ihomPointEquiv K X (yonedaEquiv.symm b) = d) :
    (T ⟶ pullback ((pre (fatJoinInclRight Δ[0] K)).app X) (yonedaEquiv.symm b)) ≃
      {g : fatJoin Δ[0] K ⟶ (ihom T).obj X //
        fatJoinInclRight Δ[0] K ≫ g = d ≫ constDiagram T X} where
  toFun f := ⟨ihomSwap _ _ X (f ≫ pullback.fst _ _), by
    rw [← ihomSwap_comp_pre_app, Category.assoc, pullback.condition, ← Category.assoc,
      stdSimplex.isTerminalObj₀.hom_ext (f ≫ pullback.snd _ _)
        (stdSimplex.isTerminalObj₀.from T), ihomSwap_from_comp, hb]⟩
  invFun g := pullback.lift ((ihomSwap _ _ X).symm g.1) (stdSimplex.isTerminalObj₀.from T) (by
    apply (ihomSwap T K X).injective
    rw [ihomSwap_comp_pre_app, Equiv.apply_symm_apply, g.2, ihomSwap_from_comp, hb])
  left_inv f := pullback.hom_ext (by rw [pullback.lift_fst, Equiv.symm_apply_apply])
    (stdSimplex.isTerminalObj₀.hom_ext _ _)
  right_inv g := Subtype.ext ((congrArg (ihomSwap T (fatJoin Δ[0] K) X)
    (pullback.lift_fst _ _ _)).trans (Equiv.apply_symm_apply _ _))

private lemma coe_fatConeFiberHomEquiv (T : SSet.{u}) (d : K ⟶ X)
    {b : ((ihom K).obj X) _⦋0⦌} (hb : ihomPointEquiv K X (yonedaEquiv.symm b) = d)
    (f : T ⟶ pullback ((pre (fatJoinInclRight Δ[0] K)).app X) (yonedaEquiv.symm b)) :
    (fatConeFiberHomEquiv T d hb f).1 = ihomSwap _ _ X (f ≫ pullback.fst _ _) :=
  rfl

private noncomputable def fatConeFiberEquiv (T : SSet.{u}) (d : K ⟶ X)
    {b : ((ihom K).obj X) _⦋0⦌} (hb : ihomPointEquiv K X (yonedaEquiv.symm b) = d) :
    (T ⟶ pullback ((pre (fatJoinInclRight Δ[0] K)).app X) (yonedaEquiv.symm b)) ≃
      (T ⟶ (fatSlice K).obj (Under.mk d)) :=
  (fatConeFiberHomEquiv T d hb).trans ((fatConeEquiv T d).trans
    (({ toFun ψ := Under.homMk ψ.1 ψ.2
        invFun φ := ⟨φ.right, Under.w φ⟩
        left_inv _ := rfl
        right_inv _ := rfl } : {ψ : fatJoin T K ⟶ X // fatJoinInclRight T K ≫ ψ = d} ≃
          ((fatJoinRightUnder K).obj T ⟶ Under.mk d)).trans
      ((fatJoinRightUnderAdjunction K).homEquiv T (Under.mk d))))

private lemma fatConeDesc_eq_fatJoinMap_comp {T T' : SSet.{u}} (f : T' ⟶ T) (d : K ⟶ X)
    (g : fatJoin Δ[0] K ⟶ (ihom T).obj X)
    (hg : fatJoinInclRight Δ[0] K ≫ g = d ≫ constDiagram T X)
    (g' : fatJoin Δ[0] K ⟶ (ihom T').obj X)
    (hg' : fatJoinInclRight Δ[0] K ≫ g' = d ≫ constDiagram T' X) (e : g' = g ≫ (pre f).app X) :
    fatConeDesc d g' hg' = fatJoinMap f (𝟙 K) ≫ fatConeDesc d g hg := by
  subst e
  refine fatJoin_hom_ext ?_ ?_ ?_
  · rw [fatConeDesc, fatJoinInclLeft_fatJoinDesc, fatJoinInclLeft_fatJoinMap_assoc, fatConeDesc,
      fatJoinInclLeft_fatJoinDesc, ← Category.assoc, ihomPointEquiv_comp_pre_app]
  · rw [fatConeDesc, fatJoinInclRight_fatJoinDesc, fatJoinInclRight_fatJoinMap_assoc,
      Category.id_comp, fatConeDesc, fatJoinInclRight_fatJoinDesc]
  · rw [fatConeDesc, fatJoinCyl_fatJoinDesc, fatJoinCyl_fatJoinMap_assoc, fatConeDesc,
      fatJoinCyl_fatJoinDesc, ← Category.assoc, uncurry_pre_app]
    have : (fatConeShuffle T' Δ[1] K).inv ≫ f ▷ _ =
        Δ[1] ◁ (f ⊗ₘ 𝟙 K) ≫ (fatConeShuffle T Δ[1] K).inv := by
      ext1
      · simp [fatConeShuffle]
      ext1
      · simp [fatConeShuffle]
      ext1
      · exact stdSimplex.isTerminalObj₀.hom_ext _ _
      · simp [fatConeShuffle]
    rw [reassoc_of% this]

private lemma fatConeFiberEquiv_comp {T T' : SSet.{u}} (d : K ⟶ X)
    {b : ((ihom K).obj X) _⦋0⦌} (hb : ihomPointEquiv K X (yonedaEquiv.symm b) = d) (f : T' ⟶ T)
    (g : T ⟶ pullback ((pre (fatJoinInclRight Δ[0] K)).app X) (yonedaEquiv.symm b)) :
    fatConeFiberEquiv T' d hb (f ≫ g) = f ≫ fatConeFiberEquiv T d hb g := by
  simp only [fatConeFiberEquiv, Equiv.trans_apply]
  rw [← Adjunction.homEquiv_naturality_left]
  congr 1
  ext1
  exact fatConeDesc_eq_fatJoinMap_comp f d _ (fatConeFiberHomEquiv T d hb g).2 _
    (fatConeFiberHomEquiv T' d hb (f ≫ g)).2 (by
    rw [coe_fatConeFiberHomEquiv, coe_fatConeFiberHomEquiv, Category.assoc, ihomSwap_comp])

noncomputable def fatConeFiberIso (d : K ⟶ X) {b : ((ihom K).obj X) _⦋0⦌}
    (hb : ihomPointEquiv K X (yonedaEquiv.symm b) = d) :
    pullback ((pre (fatJoinInclRight Δ[0] K)).app X) (yonedaEquiv.symm b) ≅
      (fatSlice K).obj (Under.mk d) :=
  Yoneda.ext _ _ (fun {T} f ↦ fatConeFiberEquiv T d hb f)
    (fun {T} g ↦ (fatConeFiberEquiv T d hb).symm g) (fun _ ↦ Equiv.symm_apply_apply _ _)
    (fun _ ↦ Equiv.apply_symm_apply _ _) (fun f g ↦ fatConeFiberEquiv_comp d hb f g)

private lemma comp_fatConeFiberIso_hom (d : K ⟶ X) {b : ((ihom K).obj X) _⦋0⦌}
    (hb : ihomPointEquiv K X (yonedaEquiv.symm b) = d) {T : SSet.{u}}
    (f : T ⟶ pullback ((pre (fatJoinInclRight Δ[0] K)).app X) (yonedaEquiv.symm b)) :
    f ≫ (fatConeFiberIso d hb).hom = fatConeFiberEquiv T d hb f :=
  (fatConeFiberEquiv_comp d hb f (𝟙 _)).symm.trans (congrArg _ (Category.comp_id f))

private lemma ihomSwap_ihomPointEquiv_symm {A : SSet.{u}} (φ : A ⟶ X) :
    ihomSwap Δ[0] A X ((ihomPointEquiv A X).symm φ) = φ ≫ constDiagram Δ[0] X := by
  rw [ihomSwap_apply, curry_eq_iff, uncurry_ihomPointEquiv_symm, uncurry_natural_left,
    uncurry_constDiagram, whiskerLeft_snd, braiding_hom_fst_assoc]

private lemma ihomPointEquiv_comp_constDiagram (k : Δ[0] ⟶ X) :
    ihomPointEquiv Δ[0] X (k ≫ constDiagram Δ[0] X) = k := by
  rw [ihomPointEquiv_apply, uncurry_natural_left, uncurry_constDiagram, whiskerLeft_snd,
    lift_snd_assoc, stdSimplex.isTerminalObj₀.hom_ext (stdSimplex.isTerminalObj₀.from _) (𝟙 _),
    Category.id_comp]

private lemma fatConeDesc_eq_of_eq_comp_constDiagram (d : K ⟶ X) (φ : fatJoin Δ[0] K ⟶ X)
    (hφ : fatJoinInclRight Δ[0] K ≫ φ = d) (g : fatJoin Δ[0] K ⟶ (ihom Δ[0]).obj X)
    (hg : fatJoinInclRight Δ[0] K ≫ g = d ≫ constDiagram Δ[0] X)
    (e : g = φ ≫ constDiagram Δ[0] X) : fatConeDesc d g hg = φ := by
  subst e
  refine (fatJoin_hom_ext ?_ ?_ ?_).symm
  · rw [fatConeDesc, fatJoinInclLeft_fatJoinDesc, ← Category.assoc,
      ihomPointEquiv_comp_constDiagram]
  · rw [fatConeDesc, fatJoinInclRight_fatJoinDesc, hφ]
  · have : (fatConeShuffle Δ[0] Δ[1] K).inv ≫ snd _ _ = 𝟙 _ := by
      ext1
      · simp [fatConeShuffle]
      ext1
      · exact stdSimplex.isTerminalObj₀.hom_ext _ _
      · simp [fatConeShuffle]
    rw [fatConeDesc, fatJoinCyl_fatJoinDesc, ← Category.assoc, uncurry_natural_left,
      uncurry_constDiagram, whiskerLeft_snd, reassoc_of% this]

lemma fatConeFiberIso_hom_app_fiberVertex (d : K ⟶ X) {b : ((ihom K).obj X) _⦋0⦌}
    (hb : ihomPointEquiv K X (yonedaEquiv.symm b) = d) (φ : fatJoin Δ[0] K ⟶ X)
    (hφ : fatJoinInclRight Δ[0] K ≫ φ = d)
    (h : ((pre (fatJoinInclRight Δ[0] K)).app X).app _
      (yonedaEquiv ((ihomPointEquiv _ X).symm φ)) = b) :
    (fatConeFiberIso d hb).hom.app _ (fiberVertex _ _ h) =
      yonedaEquiv ((fatJoinRightUnderAdjunction K).homEquiv Δ[0] (Under.mk d)
        (Under.homMk φ hφ)) := by
  rw [← Equiv.apply_symm_apply yonedaEquiv (fiberVertex _ _ h), ← yonedaEquiv_comp,
    comp_fatConeFiberIso_hom]
  simp only [fatConeFiberEquiv, Equiv.trans_apply]
  congr 2
  ext1
  refine fatConeDesc_eq_of_eq_comp_constDiagram d φ hφ _ (fatConeFiberHomEquiv Δ[0] d hb _).2 ?_
  rw [coe_fatConeFiberHomEquiv, yonedaEquiv_symm_fiberVertex_fst,
    Equiv.symm_apply_apply, ihomSwap_ihomPointEquiv_symm]

lemma joinAdjunct_sliceToFatSlice_app (c : join Δ[0] K ⟶ X) :
    joinAdjunct c ≫ (sliceToFatSlice K).app _ =
      (fatJoinRightUnderAdjunction K).homEquiv _ _
        (Under.homMk (fatJoinToJoin Δ[0] K ≫ c) (fatJoinInclRight_fatJoinToJoin_assoc _ _ _)) := by
  apply ((fatJoinRightUnderAdjunction K).homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    sliceToFatSlice, conjugateEquiv_counit, NatTrans.naturality_assoc, joinAdjunct,
    ← Adjunction.homEquiv_counit, Equiv.symm_apply_apply]
  rfl

end FatConeFibre

end SSet
