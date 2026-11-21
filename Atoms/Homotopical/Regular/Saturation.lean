import Atoms.Homotopical.Localizer.LeftProper
import Atoms.Homotopical.Regular.ElementsRestriction
import Atoms.Homotopical.Regular.Union

open CategoryTheory Limits MorphismProperty

namespace Atoms.Homotopical

universe v

variable {A : Type v} [SmallCategory A]

section Restrict

variable {X : Aᵒᵖ ⥤ Type v} {G : CostructuredArrow yoneda X ⥤ Aᵒᵖ ⥤ Type v}
  (π : G ⟶ representablesOver X)

noncomputable def colimitDescRestrict {Y : Aᵒᵖ ⥤ Type v} (m : Y ⟶ X) :
    colimit (CostructuredArrow.map m ⋙ G) ⟶ Y :=
  colimit.desc _
    { pt := Y
      ι := Functor.whiskerLeft (CostructuredArrow.map m) π ≫
        (Presheaf.tautologicalCocone Y).ι }

@[reassoc]
theorem ι_colimitDescRestrict {Y : Aᵒᵖ ⥤ Type v} (m : Y ⟶ X) (c : CostructuredArrow yoneda Y) :
    colimit.ι (CostructuredArrow.map m ⋙ G) c ≫ colimitDescRestrict π m =
      π.app ((CostructuredArrow.map m).obj c) ≫ c.hom :=
  colimit.ι_desc _ c

theorem map_comp_app_comp_eq_app_comp_yoneda_map {c c' : CostructuredArrow yoneda X}
    (φ : c ⟶ c') {Z : Aᵒᵖ ⥤ Type v} (h : yoneda.obj c'.left ⟶ Z) :
    G.map φ ≫ π.app c' ≫ h = π.app c ≫ yoneda.map φ.left ≫ h :=
  π.naturality_assoc φ h

theorem colimitPreMap_comp_colimitDescRestrict {Z Y : Aᵒᵖ ⥤ Type v} (m : Z ⟶ Y) (g : Y ⟶ X)
    {k : Z ⟶ X} (hk : m ≫ g = k) :
    colimitPreMap m g hk G ≫ colimitDescRestrict π g = colimitDescRestrict π k ≫ m := by
  refine colimit.hom_ext fun c ↦ ?_
  rw [ι_colimitPreMap_assoc, ι_colimitDescRestrict, ι_colimitDescRestrict_assoc,
    map_comp_app_comp_eq_app_comp_yoneda_map]
  simp only [CostructuredArrow.homMk_left, CostructuredArrow.map_obj_hom]
  erw [yoneda.map_id, Category.id_comp]
  exact (Category.assoc _ _ _).symm

@[simps]
def toMapCompMap {Y : Aᵒᵖ ⥤ Type v} (i : X ⟶ Y) (r : Y ⟶ X) (hir : i ≫ r = 𝟙 X) :
    𝟭 (CostructuredArrow yoneda X) ⟶ CostructuredArrow.map i ⋙ CostructuredArrow.map r where
  app c := CostructuredArrow.homMk (𝟙 c.left) (by simp [hir])
  naturality _ _ _ := CostructuredArrow.hom_ext _ _ (by simp)

variable (G) in
noncomputable def colimitSectionOfRetract {Y : Aᵒᵖ ⥤ Type v} (i : X ⟶ Y) (r : Y ⟶ X)
    (hir : i ≫ r = 𝟙 X) : colimit G ⟶ colimit (CostructuredArrow.map r ⋙ G) :=
  colimit.desc G
    { pt := colimit (CostructuredArrow.map r ⋙ G)
      ι := (Functor.whiskerRight (toMapCompMap i r hir) G : G ⟶ _) ≫
        Functor.whiskerLeft (CostructuredArrow.map i)
          (colimit.cocone (CostructuredArrow.map r ⋙ G)).ι }

variable (G) in
@[reassoc]
theorem ι_colimitSectionOfRetract {Y : Aᵒᵖ ⥤ Type v} (i : X ⟶ Y) (r : Y ⟶ X)
    (hir : i ≫ r = 𝟙 X) (c : CostructuredArrow yoneda X) :
    colimit.ι G c ≫ colimitSectionOfRetract G i r hir =
      G.map ((toMapCompMap i r hir).app c) ≫
        colimit.ι (CostructuredArrow.map r ⋙ G) ((CostructuredArrow.map i).obj c) :=
  colimit.ι_desc _ c

variable (G) in
theorem colimitSectionOfRetract_comp_pre {Y : Aᵒᵖ ⥤ Type v} (i : X ⟶ Y) (r : Y ⟶ X)
    (hir : i ≫ r = 𝟙 X) :
    colimitSectionOfRetract G i r hir ≫ colimit.pre G (CostructuredArrow.map r) = 𝟙 _ := by
  refine colimit.hom_ext fun c ↦ ?_
  rw [ι_colimitSectionOfRetract_assoc, colimit.ι_pre, Category.comp_id]
  exact colimit.w G ((toMapCompMap i r hir).app c)

@[reassoc]
theorem ι_colimitSectionOfRetract_colimitDescRestrict {Y : Aᵒᵖ ⥤ Type v} (i : X ⟶ Y)
    (r : Y ⟶ X) (hir : i ≫ r = 𝟙 X) (c : CostructuredArrow yoneda X) :
    colimit.ι G c ≫ colimitSectionOfRetract G i r hir ≫ colimitDescRestrict π r =
      π.app c ≫ c.hom ≫ i := by
  rw [ι_colimitSectionOfRetract_assoc, ι_colimitDescRestrict,
    map_comp_app_comp_eq_app_comp_yoneda_map]
  simp only [CostructuredArrow.homMk_left, toMapCompMap_app, CostructuredArrow.map_obj_hom]
  erw [yoneda.map_id, Category.id_comp]

end Restrict

theorem colimit_pre_comp_regularizationMap {X Y : Aᵒᵖ ⥤ Type v} (g : Y ⟶ X) :
    colimit.pre ((projectiveReplacement A _).obj (representablesOver X))
        (CostructuredArrow.map g) ≫ regularizationMap X =
      colimitDescRestrict ((projectiveReplacementπ A _).app (representablesOver X)) g ≫ g := by
  refine colimit.hom_ext fun c ↦ ?_
  rw [colimit.ι_pre_assoc, ι_regularizationMap, ι_colimitDescRestrict_assoc]
  exact (Category.assoc _ _ _).symm

theorem colimitSectionOfRetract_comp_colimitDescRestrict {X Y : Aᵒᵖ ⥤ Type v} (i : X ⟶ Y)
    (r : Y ⟶ X) (hir : i ≫ r = 𝟙 X) :
    colimitSectionOfRetract _ i r hir ≫
        colimitDescRestrict ((projectiveReplacementπ A _).app (representablesOver X)) r =
      regularizationMap X ≫ i := by
  refine colimit.hom_ext fun c ↦ ?_
  rw [ι_colimitSectionOfRetract_colimitDescRestrict, ← Category.assoc (colimit.ι _ c),
    ι_regularizationMap]
  exact (Category.assoc _ _ _).symm

theorem projectiveCofibrations_initial_to_map_comp_projectiveReplacement
    {X Y : Aᵒᵖ ⥤ Type v} (m : Y ⟶ X) :
    projectiveCofibrations A (CostructuredArrow yoneda Y)
      (initial.to (CostructuredArrow.map m ⋙
        (projectiveReplacement A _).obj (representablesOver X))) :=
  projectiveCofibrations_initial_to_comp _ (projectiveCofibrations_whiskerLeft_map m
    (projectiveCofibrations_initial_to_projectiveReplacement _))

theorem IsAccessibleALocalizer.colimitDescRestrict_mem {V : MorphismProperty (Aᵒᵖ ⥤ Type v)}
    [hV : IsAccessibleALocalizer V] {X Y : Aᵒᵖ ⥤ Type v} (m : Y ⟶ X) (hY : IsRegular V Y) :
    V (colimitDescRestrict ((projectiveReplacementπ A _).app (representablesOver X)) m) :=
  hV.mem_of_isRegular_resolution hY
    (projectiveCofibrations_initial_to_map_comp_projectiveReplacement m)
    (Functor.whiskerLeft (CostructuredArrow.map m)
      ((projectiveReplacementπ A _).app (representablesOver X)))
    (fun c ↦ hV.isALocalizer.rlp_monomorphisms_le _
      (rlp_monomorphisms_projectiveReplacementπ_app (representablesOver X)
        ((CostructuredArrow.map m).obj c))) _ (ι_colimitDescRestrict _ m)

theorem IsAccessibleALocalizer.isRegular_of_isPushout
    {V : MorphismProperty (Aᵒᵖ ⥤ Type v)} [hV : IsAccessibleALocalizer V]
    {X₀ X₁ X₂ X : Aᵒᵖ ⥤ Type v} {f₁ : X₀ ⟶ X₁} {f₂ : X₀ ⟶ X₂} {g₁ : X₁ ⟶ X} {g₂ : X₂ ⟶ X}
    (h : IsPushout f₁ f₂ g₁ g₂) [Mono f₁] (h₀ : IsRegular V X₀) (h₁ : IsRegular V X₁)
    (h₂ : IsRegular V X₂) : IsRegular V X := by
  have := mono_colimitPreMap f₁ g₁ rfl _
    (projectiveCofibrations_initial_to_map_comp_projectiveReplacement g₁)
  exact hV.isALocalizer.of_isPushout_of_mono (isPushout_colimitPreMap h rfl h.w.symm _) h
    _ _ _ (regularizationMap X)
    (colimitPreMap_comp_colimitDescRestrict _ f₁ g₁ rfl)
    (colimitPreMap_comp_colimitDescRestrict _ f₂ g₂ h.w.symm)
    (colimit_pre_comp_regularizationMap g₁) (colimit_pre_comp_regularizationMap g₂)
    (hV.colimitDescRestrict_mem _ h₀) (hV.colimitDescRestrict_mem _ h₁)
    (hV.colimitDescRestrict_mem _ h₂)

theorem IsAccessibleALocalizer.isRegular_of_retract
    {V : MorphismProperty (Aᵒᵖ ⥤ Type v)} [hV : IsAccessibleALocalizer V]
    {X Y : Aᵒᵖ ⥤ Type v} (i : X ⟶ Y) (r : Y ⟶ X) (hir : i ≫ r = 𝟙 X) (hY : IsRegular V Y) :
    IsRegular V X := by
  let R : RetractArrow (regularizationMap X)
      (colimitDescRestrict ((projectiveReplacementπ A _).app (representablesOver X)) r) :=
    { i := Arrow.homMk (colimitSectionOfRetract _ i r hir) i
        (colimitSectionOfRetract_comp_colimitDescRestrict i r hir)
      r := Arrow.homMk (colimit.pre _ (CostructuredArrow.map r)) r
        (colimit_pre_comp_regularizationMap r)
      retract := Arrow.hom_ext _ _ (colimitSectionOfRetract_comp_pre _ i r hir) hir }
  exact hV.isALocalizer.isStableUnderRetracts.of_retract R (hV.colimitDescRestrict_mem r hY)

theorem IsAccessibleALocalizer.isRegular_iff_of_iso
    {V : MorphismProperty (Aᵒᵖ ⥤ Type v)} [hV : IsAccessibleALocalizer V]
    {X Y : Aᵒᵖ ⥤ Type v} (e : X ≅ Y) : IsRegular V X ↔ IsRegular V Y :=
  ⟨hV.isRegular_of_retract e.inv e.hom e.inv_hom_id,
    hV.isRegular_of_retract e.hom e.inv e.hom_inv_id⟩

theorem IsAccessibleALocalizer.isMonoSaturatedClass_isRegular
    {V : MorphismProperty (Aᵒᵖ ⥤ Type v)} [hV : IsAccessibleALocalizer V] :
    IsMonoSaturatedClass.{v, v} (IsRegular V) where
  of_isPushout hp hm h₀ h₁ h₂ := haveI := hm; hV.isRegular_of_isPushout hp h₀ h₁ h₂
  of_isColimit _ _ _ F hF _ hc h := hV.isRegular_of_isColimit F hF hc h

theorem IsAccessibleALocalizer.isRegularALocalizer_iff_of_saturation_eq
    {V : MorphismProperty (Aᵒᵖ ⥤ Type v)} [hV : IsAccessibleALocalizer V]
    (S : MorphismProperty (Aᵒᵖ ⥤ Type v))
    (hS : saturation.{v} S = MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v)) :
    IsRegularALocalizer V ↔
      ∀ {X Y : Aᵒᵖ ⥤ Type v} (f : X ⟶ Y), S f → IsRegular V X ∧ IsRegular V Y :=
  ⟨fun h _ _ _ _ ↦ ⟨h.isRegular _, h.isRegular _⟩, fun hgen ↦
    ⟨forall_of_saturation_eq hV.isMonoSaturatedClass_isRegular
      (fun i r hir hY ↦ hV.isRegular_of_retract i r hir hY) S hS hgen⟩⟩

end Atoms.Homotopical
