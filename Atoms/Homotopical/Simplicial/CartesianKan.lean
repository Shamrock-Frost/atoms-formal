import Atoms.Homotopical.Simplicial.Cartesian
import Atoms.Homotopical.Simplicial.JoyalKan

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra Simplicial

universe u

namespace Atoms.Homotopical

theorem cartesian_isFibrant_sharp_of_kanComplex (K : SSet.{u}) [K.KanComplex] :
    cartesianCylinder.{u}.IsFibrant cartesianGenerators
      ((MarkedPresheaf.sharp edgeMarking).obj K) :=
  (MarkedSSet.modelCategoryCartesian.isFibrant_iff_isFibrant _).1
    ((MarkedSSet.modelCategoryCartesian.isFibrant_iff _).2
      ⟨inferInstanceAs (SSet.Quasicategory K),
        fun e => ⟨fun _ => SSet.nonempty_invStruct_of_kanComplex K e,
          fun _ => (MarkedPresheaf.mem_marked_sharp _ _ _ _).2 rfl⟩⟩)

theorem kanWeak_forget_map_of_cartesianWeak {X Y : MarkedSSet.{u}} (f : X ⟶ Y)
    (hf : cartesianCylinder.{u}.weakEquivalences cartesianGenerators f) :
    kanWeak (MarkedPresheaf.forget.map f) := by
  refine ExactCylinder.map_mem_weakEquivalences cartesianCylinder.{u} simplicialCylinder.{u}
    cartesianGenerators ⊥ (MarkedPresheaf.forgetSharpAdjunction edgeMarking) ?_ ?_ f hf
  · intro Z
    have hc := congr_app cartesianCylinderForgetIso_hom_comp_whiskerLeft_contraction Z
    change (cartesianCylinderForgetIso.app Z).hom ≫
      joyalInterval.{u}.cylinder.contraction.app (MarkedPresheaf.forget.obj Z) =
        MarkedPresheaf.forget.map (cartesianCylinder.{u}.contraction.app Z) at hc
    rw [← hc]
    exact kanWeak.comp_mem _ _
      (isomorphisms_le_of_containsIdentities kanWeak _ (isomorphisms.infer_property _))
      (joyal_weakEquivalences_le_kanWeak _
        (joyalInterval.{u}.cylinder.contraction_mem_weakEquivalences _
          SSet.innerHornInclusions_le_monomorphisms _))
  · intro K hK
    have := (isFibrant_bot_iff_kanComplex K).1 hK
    exact cartesian_isFibrant_sharp_of_kanComplex K

open MarkedSSet.modelCategoryCartesian SSet.modelCategoryQuillen in
theorem isQuillen_forgetSharpAdjunction_kan :
    (MarkedPresheaf.forgetSharpAdjunction edgeMarking).IsQuillen where
  cofibrations_le _ _ f hf := by
    have : Mono f := hf
    exact MarkedPresheaf.forget.map_mono f
  trivialCofibrations_le _ _ f hf := by
    have : Mono f := hf.1
    exact ⟨MarkedPresheaf.forget.map_mono f,
      kanWeak_forget_map_of_cartesianWeak f hf.2⟩

end Atoms.Homotopical
