import Atoms.Diagrammatic.ClosedSubpresheaf

open CategoryTheory Limits Opposite Order Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape

universe u

namespace Atoms.Diagrammatic

def realize : RDCpx.{0} ⥤ DiagSet.{u} :=
  uliftYoneda.{u} ⋙ (Functor.whiskeringLeft Atomᵒᵖ RDCpx.{0}ᵒᵖ (Type u)).obj atomToRDCpx.op

theorem realize_obj_obj (P : RDCpx.{0}) (T : Atom) :
    (realize.{u}.obj P).obj (op T) = ULift.{u} (atomToRDCpx.obj T ⟶ P) :=
  rfl

def realizeAtomIso (U : Atom) : realize.{u}.obj (atomToRDCpx.obj U) ≅ ball.{u} U :=
  NatIso.ofComponents
    (fun _ => Equiv.toIso (Equiv.ulift.trans (Atom.fullyFaithful.homEquiv.symm.trans
      Equiv.ulift.symm)))
    (fun _ => rfl)

@[simp] theorem realize_map_app {P Q : RDCpx.{0}} (f : P ⟶ Q)
    {T : Atom} (c : atomToRDCpx.obj T ⟶ P) :
    (realize.{u}.map f).app (op T) ⟨c⟩ = ⟨c ≫ f⟩ := rfl

@[simp] theorem realize_obj_map (P : RDCpx.{0}) {T U : Atom}
    (f : T ⟶ U) (c : atomToRDCpx.obj U ⟶ P) :
    (realize.{u}.obj P).map f.op ⟨c⟩ = ⟨atomToRDCpx.map f ≫ c⟩ := rfl

theorem realize_map_comp_app {P Q : RDCpx.{0}} {Z : DiagSet.{u}} (φ : P ⟶ Q)
    (w : realize.obj Q ⟶ Z) {T : Atom} (c : atomToRDCpx.obj T ⟶ P) :
    (realize.map φ ≫ w).app (op T) ⟨c⟩ = w.app (op T) ⟨c ≫ φ⟩ :=
  rfl

theorem mono_realize_map {P Q : RDCpx.{0}} (f : P ⟶ Q)
    (hf : Function.Injective (ConcreteCategory.hom f.hom)) :
    Mono (realize.{u}.map f) := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨T⟩
  rw [mono_iff_injective]
  rintro ⟨g : atomToRDCpx.obj T ⟶ P⟩ ⟨g' : atomToRDCpx.obj T ⟶ P⟩ h
  simp only [realize_map_app] at h
  exact ULift.ext _ _ (WideSubcategory.hom_ext _ (ConcreteCategory.hom_ext _ _ fun t =>
    hf (congrArg (fun k : atomToRDCpx.obj T ⟶ Q => ConcreteCategory.hom k.hom t)
      (ULift.up_inj.1 h))))

def realizeSubset (P : RDCpx.{0}) (S : LowerSet P.obj.toOGP) :
    Subfunctor (realize.{u}.obj P) where
  obj T := {f : ULift.{u} (atomToRDCpx.obj T.unop ⟶ P) | ∀ t, ConcreteCategory.hom f.down.hom t ∈ S}
  map g _ hf := fun t => hf (g.unop t)

@[simp] theorem mem_realizeSubset (P : RDCpx.{0})
    (S : LowerSet P.obj.toOGP) (T : Atom) (c : (realize.{u}.obj P).obj (op T)) :
    c ∈ (realizeSubset P S).obj (op T) ↔
      ∀ t, ConcreteCategory.hom c.down.hom t ∈ S := Iff.rfl

theorem realizeSubset_univ (P : RDCpx.{0}) : realizeSubset.{u} P ⊤ = ⊤ := by
  ext ⟨T⟩ f
  exact iff_of_true (fun _ => LowerSet.mem_top) trivial

theorem realizeSubset_inter (P : RDCpx.{0}) (S T : LowerSet P.obj.toOGP) :
    realizeSubset.{u} P (S ⊓ T) = realizeSubset P S ⊓ realizeSubset P T := by
  ext ⟨U⟩ f
  simp only [mem_realizeSubset]
  exact forall_and

theorem realizeSubset_union (P : RDCpx.{0}) (S T : LowerSet P.obj.toOGP) :
    realizeSubset.{u} P (S ⊔ T) = realizeSubset P S ⊔ realizeSubset P T := by
  ext ⟨U⟩ f
  simp only [mem_realizeSubset]
  constructor
  · intro h
    rcases h U.top with hs | ht
    · exact Or.inl (apply_mem_of_apply_top_mem f.down hs)
    · exact Or.inr (apply_mem_of_apply_top_mem f.down ht)
  · rintro (h | h) t
    · exact Or.inl (h t)
    · exact Or.inr (h t)

def realizeRestrictIso (P : RDCpx.{0}) (S : LowerSet P.obj.toOGP)
    (G : Subfunctor (realize.{u}.obj P)) (h : realizeSubset P S = G) :
    realize.obj (RDCpx.restrict P S) ≅ G.toFunctor :=
  NatIso.ofComponents
    (fun _ =>
      { hom := ↾fun g => ⟨⟨g.down ≫ RDCpx.restrictIncl P S⟩,
          h ▸ fun t => (ConcreteCategory.hom g.down.hom t).2⟩
        inv := ↾fun f => ⟨restrictLift P S f.1.down
          (h.symm ▸ f.2 : f.1 ∈ (realizeSubset P S).obj _)⟩
        hom_inv_id := rfl
        inv_hom_id := rfl })
    (fun _ => rfl)

theorem realizeSubset_atom (U : Atom) (S : LowerSet U.ogp) (T : Atom)
    (f : atomToRDCpx.obj T ⟶ atomToRDCpx.obj U) :
    ULift.up f ∈ (realizeSubset.{u} (atomToRDCpx.obj U) S).obj (op T) ↔
      ((realizeAtomIso.{u} U).hom.app (op T) ⟨f⟩) ∈ (closedSubpresheaf U S).obj (op T) :=
  Iff.rfl

def realizeSubsetAtomIso (U : Atom) (S : LowerSet U.ogp) :
    (realizeSubset.{u} (atomToRDCpx.obj U) S).toFunctor ≅ (closedSubpresheaf U S).toFunctor where
  hom := Subfunctor.lift ((realizeSubset (atomToRDCpx.obj U) S).ι ≫ (realizeAtomIso U).hom) (by
    rintro ⟨T⟩ _ ⟨f, rfl⟩
    exact f.2)
  inv := Subfunctor.lift ((closedSubpresheaf U S).ι ≫ (realizeAtomIso U).inv) (by
    rintro ⟨T⟩ _ ⟨g, rfl⟩
    exact g.2)
  hom_inv_id := by
    ext T f
    rfl
  inv_hom_id := by
    ext T g
    rfl

noncomputable def sphereRealizeIso (U : Atom) :
    sphere.{u} U ≅ realize.obj ((atomToRDCpx.obj U).restrict (U.ogp.bdryFull ⊤)) :=
  { hom := Subfunctor.homOfLe (closedSubpresheaf_univ_erase_top U).ge
    inv := Subfunctor.homOfLe (closedSubpresheaf_univ_erase_top U).le
    hom_inv_id := rfl
    inv_hom_id := rfl } ≪≫ (realizeSubsetAtomIso U _).symm ≪≫ (realizeRestrictIso _ _ _ rfl).symm

@[reassoc] theorem sphereRealizeIso_hom_comp (U : Atom) :
    (sphereRealizeIso.{u} U).hom ≫
      realize.map ((atomToRDCpx.obj U).restrictIncl (U.ogp.bdryFull ⊤)) =
        sphereInclusion U ≫ (realizeAtomIso U).inv :=
  rfl

@[reassoc] theorem sphereRealizeIso_inv_comp (U : Atom) :
    (sphereRealizeIso.{u} U).inv ≫ sphereInclusion U =
      realize.map ((atomToRDCpx.obj U).restrictIncl (U.ogp.bdryFull ⊤)) ≫ (realizeAtomIso U).hom :=
  rfl

end Atoms.Diagrammatic
