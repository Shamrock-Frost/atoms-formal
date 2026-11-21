import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.Isofibration
import Mathlib.AlgebraicTopology.Quasicategory.StrictBicategory
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct

open CategoryTheory MonoidalCategory MonoidalClosed Simplicial

universe u

namespace SSet

noncomputable def ihomVertex {A B : SSet.{u}} (f : A ⟶ B) : ((ihom A).obj B) _⦋0⦌ :=
  SSet.unitHomEquiv _ (curry' f)

noncomputable def coherentIsoVertex (b : Bool) : 𝟙_ SSet.{u} ⟶ coherentIso.{u} :=
  (SSet.unitHomEquiv _).symm (cond b coherentIso.x₁ coherentIso.x₀)

theorem exists_nonempty_invStruct_iff_exists_coherentIso {X : SSet.{u}} [X.Quasicategory]
    (x y : X _⦋0⦌) :
    (∃ e : Edge x y, Nonempty e.InvStruct) ↔
      ∃ G : coherentIso.{u} ⟶ X, G.app _ coherentIso.x₀ = x ∧ G.app _ coherentIso.x₁ = y := by
  refine ⟨fun ⟨e, ⟨I⟩⟩ ↦ ?_, ?_⟩
  · obtain ⟨G, hG⟩ := exists_coherentIso_extension e I
    exact ⟨G, by rw [← (coherentIso.hom.map G).src_eq, hG, e.src_eq],
      by rw [← (coherentIso.hom.map G).tgt_eq, hG, e.tgt_eq]⟩
  · rintro ⟨G, rfl, rfl⟩
    obtain ⟨I⟩ := coherentIso.nonempty_invStruct_app G coherentIso.hom.edge
    exact ⟨coherentIso.hom.map G, ⟨I.ofEq rfl⟩⟩

private lemma unitHomEquiv_coherentIsoVertex_comp {X : SSet.{u}} (G : coherentIso.{u} ⟶ X)
    (b : Bool) :
    SSet.unitHomEquiv X (coherentIsoVertex b ≫ G) =
      G.app _ (cond b coherentIso.x₁ coherentIso.x₀) := by
  have e : SSet.unitHomEquiv X (coherentIsoVertex b ≫ G) =
      G.app _ (SSet.unitHomEquiv _ (coherentIsoVertex b)) := rfl
  rw [e, coherentIsoVertex, Equiv.apply_symm_apply]

private lemma app_eq_ihomVertex_iff {A B : SSet.{u}} (G : coherentIso.{u} ⟶ (ihom A).obj B)
    (b : Bool) (h : A ⟶ B) :
    G.app _ (cond b coherentIso.x₁ coherentIso.x₀) = ihomVertex h ↔
      (λ_ A).inv ≫ coherentIsoVertex b ▷ A ≫ (β_ coherentIso A).hom ≫ uncurry G = h := by
  have e : (λ_ A).inv ≫ coherentIsoVertex b ▷ A ≫ (β_ coherentIso A).hom ≫ uncurry G =
      uncurry' (coherentIsoVertex b ≫ G) := by
    rw [BraidedCategory.braiding_naturality_left_assoc, leftUnitor_inv_braiding_assoc,
      ← uncurry_natural_left]
    rfl
  rw [e, ← unitHomEquiv_coherentIsoVertex_comp, ihomVertex, (SSet.unitHomEquiv _).injective.eq_iff]
  exact ⟨fun h' ↦ h' ▸ uncurry'_curry' h, fun h' ↦ h' ▸ (curry'_uncurry' _).symm⟩

namespace QCat

instance homCategory (A B : QCat.{u}) : Category.{u} (A ⟶ B) :=
  Bicategory.homCategory A B

instance quasicategory_obj (A : QCat.{u}) : A.obj.Quasicategory :=
  A.property

variable {A B : QCat.{u}}

private lemma nonempty_iso_iff_nonempty_iso_mk (f g : A ⟶ B) :
    Nonempty (f ≅ g) ↔
      Nonempty ((Truncated.HomotopyCategory.mk (ihomVertex f.hom) :
        ((truncation 2).obj ((ihom A.obj).obj B.obj)).HomotopyCategory) ≅
          Truncated.HomotopyCategory.mk (ihomVertex g.hom)) :=
  ⟨fun ⟨α⟩ ↦ ⟨⟨CatEnrichedOrdinary.Hom.base α.hom, CatEnrichedOrdinary.Hom.base α.inv,
      congrArg CatEnrichedOrdinary.Hom.base α.hom_inv_id,
      congrArg CatEnrichedOrdinary.Hom.base α.inv_hom_id⟩⟩,
    fun ⟨φ⟩ ↦ ⟨⟨CatEnrichedOrdinary.Hom.mk φ.hom, CatEnrichedOrdinary.Hom.mk φ.inv,
      congrArg CatEnrichedOrdinary.Hom.mk φ.hom_inv_id,
      congrArg CatEnrichedOrdinary.Hom.mk φ.inv_hom_id⟩⟩⟩

theorem nonempty_iso_iff_nonempty_invStruct (f g : A ⟶ B) :
    Nonempty (f ≅ g) ↔
      ∃ e : Edge (ihomVertex f.hom) (ihomVertex g.hom), Nonempty e.InvStruct := by
  rw [nonempty_iso_iff_nonempty_iso_mk]
  refine ⟨fun ⟨φ⟩ ↦ ?_, fun ⟨e, ⟨I⟩⟩ ↦ ⟨@asIso _ _ _ _ _ I.isIso_homMk⟩⟩
  obtain ⟨e, he⟩ := Truncated.HomotopyCategory.homMk_surjective φ.hom
  exact ⟨Edge.ofTruncated e, (isIso_homMk_iff _).1 (he ▸ inferInstance)⟩

theorem nonempty_iso_iff_exists_coherentIso (f g : A ⟶ B) :
    Nonempty (f ≅ g) ↔
      ∃ H : coherentIso.{u} ⊗ A.obj ⟶ B.obj,
        (λ_ A.obj).inv ≫ coherentIsoVertex false ▷ A.obj ≫ H = f.hom ∧
        (λ_ A.obj).inv ≫ coherentIsoVertex true ▷ A.obj ≫ H = g.hom := by
  rw [nonempty_iso_iff_nonempty_invStruct, exists_nonempty_invStruct_iff_exists_coherentIso]
  refine ⟨fun ⟨G, h₀, h₁⟩ ↦ ⟨(β_ _ _).hom ≫ uncurry G,
    (app_eq_ihomVertex_iff G false f.hom).1 h₀, (app_eq_ihomVertex_iff G true g.hom).1 h₁⟩,
    fun ⟨H, h₀, h₁⟩ ↦ ?_⟩
  have e : (β_ coherentIso A.obj).hom ≫ uncurry (curry ((β_ A.obj coherentIso).hom ≫ H)) = H := by
    rw [uncurry_curry, SymmetricCategory.symmetry_assoc]
  exact ⟨curry ((β_ A.obj coherentIso).hom ≫ H), (app_eq_ihomVertex_iff _ false _).2 (e ▸ h₀),
    (app_eq_ihomVertex_iff _ true _).2 (e ▸ h₁)⟩

def ihomObj (A : SSet.{u}) (B : QCat.{u}) : QCat.{u} :=
  ⟨(ihom A).obj B.obj, inferInstance⟩

noncomputable def pre {X Y : SSet.{u}} (u : X ⟶ Y) (B : QCat.{u}) :
    ihomObj Y B ⟶ ihomObj X B :=
  ObjectProperty.homMk ((MonoidalClosed.pre u).app B.obj)

@[simp]
lemma pre_hom {X Y : SSet.{u}} (u : X ⟶ Y) (B : QCat.{u}) :
    (pre u B).hom = (MonoidalClosed.pre u).app B.obj :=
  rfl

end QCat

end SSet
