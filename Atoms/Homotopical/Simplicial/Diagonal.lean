import Atoms.ForMathlib.AlgebraicTopology.SimplicialObject.Basic
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.Bisimplicial
import Atoms.Homotopical.Localizer.LeftProper
import Atoms.Homotopical.Simplicial.KanQuillen

open CategoryTheory Limits MonoidalCategory MorphismProperty Opposite Simplicial

universe u

namespace Atoms.Homotopical

open SSet

private theorem rlp_monomorphisms_whiskerRight {E B : SSet.{u}} {p : E ⟶ B}
    (hp : (MorphismProperty.monomorphisms SSet.{u}).rlp p) (K : SSet.{u}) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (p ▷ K) := by
  intro A A' i hi
  have := hp i hi
  refine ⟨fun {a b} sq ↦ ?_⟩
  have sq' : CommSq (a ≫ CartesianMonoidalCategory.fst _ _) i p
      (b ≫ CartesianMonoidalCategory.fst _ _) :=
    ⟨by rw [Category.assoc, ← CartesianMonoidalCategory.whiskerRight_fst, ← Category.assoc, sq.w,
      Category.assoc]⟩
  refine ⟨⟨⟨CartesianMonoidalCategory.lift sq'.lift (b ≫ CartesianMonoidalCategory.snd _ _), ?_,
    ?_⟩⟩⟩
  · refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · simp only [Category.assoc, CartesianMonoidalCategory.lift_fst, sq'.fac_left]
    · rw [Category.assoc, CartesianMonoidalCategory.lift_snd, ← reassoc_of% sq.w,
        CartesianMonoidalCategory.whiskerRight_snd]
  · refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [Category.assoc, CartesianMonoidalCategory.whiskerRight_fst,
        CartesianMonoidalCategory.lift_fst_assoc, sq'.fac_right]
    · rw [Category.assoc, CartesianMonoidalCategory.whiskerRight_snd,
        CartesianMonoidalCategory.lift_snd]

theorem kanWeak_whiskerRight {X Y : SSet.{u}} {f : X ⟶ Y} (hf : kanWeak f) (K : SSet.{u}) :
    kanWeak (f ▷ K) := by
  have := simplicialCylinder.{u}.hasFunctorialFactorization_anodyne ⊥ bot_le
  let F := MorphismProperty.factorizationData (simplicialCylinder.{u}.anodyne ⊥)
    (simplicialCylinder.{u}.anodyne ⊥).rlp f
  have hi : SSet.anodyneExtensions F.i := anodyne_bot_eq_anodyneExtensions.le _ F.hi
  have hpW : kanWeak F.p := kanWeak.of_precomp _ _ (anodyneExtensions_le_kanWeak _ hi)
    (by rw [F.fac]; exact hf)
  have hp := rlp_monomorphisms_of_J_rlp_of_kanWeak ((rlp_anodyne_bot_iff _).1 F.hp) hpW
  rw [← F.fac, comp_whiskerRight]
  exact kanWeak.comp_mem _ _ (anodyneExtensions_le_kanWeak _ (hi.whiskerRight K))
    (isALocalizer_kanWeak.rlp_monomorphisms_le _ (rlp_monomorphisms_whiskerRight hp K))

section Restriction

variable {X' Y' : SSet.{u}} (g : X' ⟶ Y')

private def restr (A : X'.Subcomplex) (B : Y'.Subcomplex) (h : A ≤ B.preimage g) :
    (A : SSet.{u}) ⟶ (B : SSet.{u}) :=
  Subcomplex.lift (A.ι ≫ g) (by rw [← Subcomplex.image_eq_range, Subcomplex.image_le_iff]; exact h)

private theorem restr_ι (A : X'.Subcomplex) (B : Y'.Subcomplex) (h : A ≤ B.preimage g) :
    restr g A B h ≫ B.ι = A.ι ≫ g := rfl

private theorem kanWeak_restr_congr {A A' : X'.Subcomplex} {B B' : Y'.Subcomplex} (hA : A = A')
    (hB : B = B') {h : A ≤ B.preimage g} {h' : A' ≤ B'.preimage g} (hw : kanWeak (restr g A B h)) :
    kanWeak (restr g A' B' h') := by
  subst hA hB
  exact hw

private theorem kanWeak_restr_of_eq_bot {A : X'.Subcomplex} {B : Y'.Subcomplex} (hA : A = ⊥)
    (hB : B = ⊥) (h : A ≤ B.preimage g) : kanWeak (restr g A B h) := by
  subst hA hB
  have := IsInitial.isIso_to (Subcomplex.isInitialBot (X := Y')) (restr g ⊥ ⊥ h)
  exact isALocalizer_kanWeak.isomorphisms_le _ (isomorphisms.infer_property _)

private theorem range_le_preimage_range {P Q : SSet.{u}} (iX : P ⟶ X') (iY : Q ⟶ Y') (g' : P ⟶ Q)
    (w : iX ≫ g = g' ≫ iY) : Subcomplex.range iX ≤ (Subcomplex.range iY).preimage g := by
  rintro k _ ⟨x, rfl⟩
  exact ⟨g'.app k x, (ConcreteCategory.congr_hom (NatTrans.congr_app w k) x).symm⟩

private theorem kanWeak_restr_range {P Q : SSet.{u}} (iX : P ⟶ X') (iY : Q ⟶ Y') [Mono iX]
    [Mono iY] (g' : P ⟶ Q) (w : iX ≫ g = g' ≫ iY) (hg' : kanWeak g') :
    kanWeak (restr g (Subcomplex.range iX) (Subcomplex.range iY)
      (range_le_preimage_range g iX iY g' w)) := by
  have e : Subcomplex.toRange iX ≫ restr g _ _ (range_le_preimage_range g iX iY g' w) =
      g' ≫ Subcomplex.toRange iY := by
    rw [← cancel_mono (Subcomplex.range iY).ι, Category.assoc, restr_ι, Category.assoc,
      Subcomplex.toRange_ι, Subcomplex.toRange_ι_assoc, w]
  have hiso : ∀ {S T : SSet.{u}} (e : S ⟶ T) [IsIso e], kanWeak e :=
    fun e _ ↦ isALocalizer_kanWeak.isomorphisms_le _ (isomorphisms.infer_property e)
  exact kanWeak.of_precomp _ _ (hiso _) (by rw [e]; exact kanWeak.comp_mem _ _ hg' (hiso _))

private theorem kanWeak_restr_sup {A₂ A₃ : X'.Subcomplex} {B₂ B₃ : Y'.Subcomplex}
    (h₂ : A₂ ≤ B₂.preimage g) (h₃ : A₃ ≤ B₃.preimage g)
    (w₀ : kanWeak (restr g (A₂ ⊓ A₃) (B₂ ⊓ B₃) (by
      rw [Subcomplex.preimage_min]; exact inf_le_inf h₂ h₃)))
    (w₂ : kanWeak (restr g A₂ B₂ h₂)) (w₃ : kanWeak (restr g A₃ B₃ h₃)) :
    kanWeak (restr g (A₂ ⊔ A₃) (B₂ ⊔ B₃) (by
      rw [Subcomplex.preimage_max]; exact sup_le_sup h₂ h₃)) := by
  have sqX : Subcomplex.BicartSq (A₂ ⊓ A₃) A₂ A₃ (A₂ ⊔ A₃) := ⟨rfl, rfl⟩
  have sqY : Subcomplex.BicartSq (B₂ ⊓ B₃) B₂ B₃ (B₂ ⊔ B₃) := ⟨rfl, rfl⟩
  exact isALocalizer_kanWeak.of_isPushout_of_mono sqX.isPushout sqY.isPushout _ _ _ _ rfl rfl rfl
    rfl w₀ w₂ w₃

end Restriction

namespace Bisimplicial

variable {X Y : SimplicialObject SSet.{u}} (f : X ⟶ Y) (hf : ∀ n, kanWeak (f.app n))
include hf

private theorem kanWeak_latchingFiltration (j : ℕ) (m : ℕ) (hj : j ≤ m + 1) :
    kanWeak (restr (f.app _) (latchingFiltration X m j) (latchingFiltration Y m j)
      (latchingFiltration_le_preimage f m j)) := by
  induction j generalizing m with
  | zero =>
    exact kanWeak_restr_of_eq_bot _ (latchingFiltration_zero X m) (latchingFiltration_zero Y m) _
  | succ j ih =>
    have hj' : j < m + 1 := hj
    refine kanWeak_restr_congr _ (latchingFiltration_succ X m j hj').symm
      (latchingFiltration_succ Y m j hj').symm (kanWeak_restr_sup _ _
      (range_le_preimage_range _ (X.σ ⟨j, hj'⟩) (Y.σ ⟨j, hj'⟩) (f.app _) (f.naturality _)) ?_
      (ih m (by lia)) ?_)
    · cases m with
      | zero =>
        obtain rfl : j = 0 := by lia
        exact kanWeak_restr_of_eq_bot _ (by rw [latchingFiltration_zero, bot_inf_eq])
          (by rw [latchingFiltration_zero, bot_inf_eq]) _
      | succ m =>
        refine kanWeak_restr_congr _ (latchingFiltration_inf_range X m ⟨j, hj'⟩).symm
          (latchingFiltration_inf_range Y m ⟨j, hj'⟩).symm
          (kanWeak_restr_range _ _ _ (restr (f.app _) (latchingFiltration X m j)
            (latchingFiltration Y m j) (latchingFiltration_le_preimage f m j)) ?_
            (ih m (by lia)))
        rw [← Category.assoc (restr _ _ _ _), restr_ι, Category.assoc]
        exact congrArg (fun t ↦ (latchingFiltration X m j).ι ≫ t)
          (f.naturality (SimplexCategory.σ ⟨j, hj'⟩).op)
    · exact kanWeak_restr_range _ (X.σ ⟨j, hj'⟩) (Y.σ ⟨j, hj'⟩) (f.app _) (f.naturality _) (hf _)

private theorem kanWeak_latching (n : ℕ) :
    kanWeak (restr (f.app _) (SSet.latching X n) (SSet.latching Y n)
      (latching_le_preimage f n)) := by
  cases n with
  | zero => exact kanWeak_restr_of_eq_bot _ (latching_zero X) (latching_zero Y) _
  | succ m =>
    exact kanWeak_restr_congr _ (latchingFiltration_self X m) (latchingFiltration_self Y m)
      (kanWeak_latchingFiltration f hf (m + 1) m le_rfl)

omit hf in
private theorem unionProd_le_preimage (n : ℕ) :
    (SSet.latching X n).unionProd ∂Δ[n] ≤
      ((SSet.latching Y n).unionProd ∂Δ[n]).preimage (f.app _ ▷ Δ[n]) := by
  rintro k ⟨y, s⟩ h
  refine (Subcomplex.mem_unionProd_iff _ _ ⟨(f.app _).app k y, s⟩).2 ?_
  rcases (Subcomplex.mem_unionProd_iff _ _ ⟨y, s⟩).1 h with hs | hy
  · exact Or.inl hs
  · exact Or.inr (latching_le_preimage f n k hy)

private theorem kanWeak_unionProd (n : ℕ) :
    kanWeak (restr (f.app _ ▷ Δ[n]) ((SSet.latching X n).unionProd ∂Δ[n])
      ((SSet.latching Y n).unionProd ∂Δ[n]) (unionProd_le_preimage f n)) := by
  let L := restr (f.app _) (SSet.latching X n) (SSet.latching Y n) (latching_le_preimage f n)
  have hL : kanWeak L := kanWeak_latching f hf n
  refine isALocalizer_kanWeak.of_isPushout_of_mono
    (Subcomplex.unionProd.isPushout (SSet.latching X n) ∂Δ[n]).flip
    (Subcomplex.unionProd.isPushout (SSet.latching Y n) ∂Δ[n]).flip
    (L ▷ _) (L ▷ _) (f.app _ ▷ _) _ (whisker_exchange _ _) ?_ ?_ ?_
    (kanWeak_whiskerRight hL _) (kanWeak_whiskerRight hL _) (kanWeak_whiskerRight (hf _) _)
  · rw [← comp_whiskerRight, ← comp_whiskerRight, restr_ι]
  · rw [← cancel_mono (Subcomplex.ι _), Category.assoc, restr_ι, Subcomplex.unionProd.ι₂_ι_assoc,
      Category.assoc, Subcomplex.unionProd.ι₂_ι, ← comp_whiskerRight, ← comp_whiskerRight, restr_ι]
  · rw [← cancel_mono (Subcomplex.ι _), Category.assoc, restr_ι, Subcomplex.unionProd.ι₁_ι_assoc,
      Category.assoc, Subcomplex.unionProd.ι₁_ι, whisker_exchange]

private theorem kanWeak_diagSkeleton (n : ℕ) :
    kanWeak (restr (diag.map f) (diagSkeleton X n) (diagSkeleton Y n)
      (diagSkeleton_le_preimage f n)) := by
  induction n with
  | zero => exact kanWeak_restr_of_eq_bot _ (diagSkeleton_zero X) (diagSkeleton_zero Y) _
  | succ n ih =>
    refine isALocalizer_kanWeak.of_isPushout_of_mono (isPushout_diagSkeleton X n)
      (isPushout_diagSkeleton Y n) (restr _ _ _ (unionProd_le_preimage f n)) (f.app _ ▷ Δ[n])
      (restr _ _ _ (diagSkeleton_le_preimage f n)) _ (restr_ι _ _ _ _).symm ?_ ?_ rfl
      (kanWeak_unionProd f hf n) (kanWeak_whiskerRight (hf _) _) ih
    · rw [← cancel_mono (Subcomplex.ι _), Category.assoc, restr_ι, Subcomplex.lift_ι_assoc,
        Category.assoc, Category.assoc, Subcomplex.lift_ι, cellMap_naturality, ← Category.assoc,
        ← Category.assoc, restr_ι]
    · rw [← cancel_mono (Subcomplex.ι _), Category.assoc, restr_ι, Subcomplex.lift_ι_assoc,
        Category.assoc, Subcomplex.lift_ι, cellMap_naturality]

end Bisimplicial

private def diagSkeletonCocone (Z : SimplicialObject SSet.{u}) :
    Cocone ((show Monotone fun j : ULift.{u} ℕ ↦ diagSkeleton Z j.down from
      fun _ _ h ↦ diagSkeleton_mono Z h).functor ⋙ Subcomplex.toSSetFunctor) where
  pt := diag.obj Z
  ι := { app j := (diagSkeleton Z j.down).ι }

private noncomputable def isColimitDiagSkeletonCocone (Z : SimplicialObject SSet.{u}) :
    IsColimit (diagSkeletonCocone Z) :=
  (isColimitOfPreserves Subcomplex.toSSetFunctor
    (CompleteLattice.colimitCocone _).isColimit).ofIsoColimit
    (Cocone.ext (Subcomplex.eqToIso (by
      rw [← iSup_diagSkeleton Z]
      exact Equiv.ulift.surjective.iSup_comp (diagSkeleton Z)) ≪≫ Subcomplex.topIso _)
      fun _ ↦ rfl)

end Atoms.Homotopical

namespace SSet

open Atoms.Homotopical

theorem kanWeak_diag_map {X Y : SimplicialObject SSet.{u}} (f : X ⟶ Y)
    (hf : ∀ n : SimplexCategoryᵒᵖ, Atoms.Homotopical.kanWeak (f.app n)) :
    Atoms.Homotopical.kanWeak (diag.map f) :=
  IsALocalizer.of_isColimit_asSmall
    (fun _ _ h ↦ inferInstanceAs (Mono (Subcomplex.homOfLE (diagSkeleton_mono X h))))
    (fun _ _ h ↦ inferInstanceAs (Mono (Subcomplex.homOfLE (diagSkeleton_mono Y h))))
    { app j := restr (diag.map f) _ _ (diagSkeleton_le_preimage f j.down) }
    (fun j ↦ Bisimplicial.kanWeak_diagSkeleton f hf j.down) (isColimitDiagSkeletonCocone X)
    (isColimitDiagSkeletonCocone Y) (diag.map f) fun _ ↦ rfl

theorem kanWeak_diag_map_of_transpose {X Y : SimplicialObject SSet.{u}} (f : X ⟶ Y)
    (hf : ∀ n : SimplexCategoryᵒᵖ, Atoms.Homotopical.kanWeak ((transpose.map f).app n)) :
    Atoms.Homotopical.kanWeak (diag.map f) :=
  (MorphismProperty.arrow_mk_iso_iff _ (Arrow.isoMk (diagTransposeIso.app X)
    (diagTransposeIso.app Y) (diagTransposeIso.hom.naturality f).symm)).1
    (kanWeak_diag_map (transpose.map f) hf)

theorem kanWeak_toDiag (X : SimplicialObject SSet.{u})
    (hX : ∀ ⦃m n : SimplexCategory⦄ (g : m ⟶ n), Atoms.Homotopical.kanWeak (X.map g.op)) :
    Atoms.Homotopical.kanWeak (toDiag X) :=
  kanWeak.comp_mem _ _ (isALocalizer_kanWeak.isomorphisms_le _ (isomorphisms.infer_property _))
    (kanWeak_diag_map _ fun n ↦ hX (SimplexCategory.isTerminalZero.from n.unop))

end SSet
