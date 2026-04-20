#
   cesm_ontology.cql
   CESM Ontology Schema — Categorical formalization of Mobus 8-tuple + Bunge CES

   Source: Systems/Mobus/Tuple.lean (8-tuple + 5 coherence constraints)
           Systems/Core/System.lean (Bunge CES triple)
           Systems/Mobus/FlowNetwork.lean (directed graphs with capacity)

   Entities map to Lean structures. Foreign keys map to structural relationships.
   Disjointness (C ∩ E = ∅) enforced by separate entity types.
   Bipartite constraint on G is a data integrity observation, not a path equation.

   Opaque fields (T, H, Δt) deferred — "carried data with no structural role."
*)

typeside Ty = literal {
  java_types
    Str = "java.lang.String"
    Int = "java.lang.Integer"
    Dbl = "java.lang.Double"
  java_fns
    concat : Str, Str -> Str = "(x, y) -> x + y"
  java_constants
    zero : Int = "0"
    empty : Str = "\"\""
}

# === CESM Schema ===

   Lean structure hierarchy:
     KlirSystem (T, R)  ←  ConcreteSystem (C, E, S)  ←  MobusSystem (C, N, E, G, B, T, H, Δt)

   CQL flattens the three layers into one schema.
   The Bridge projection (Mobus → Bunge) becomes a Delta query.
   The Klir projection (Bunge → Klir) drops further structure.
*)

schema CESM = literal : Ty {

  entities
    # Klir layer: the universal ancestor S = (T, R) *)
    Thing              # α in Lean — the node type shared by components and env objects *)
    Relation           # Set (α × α) — directed pairs, capacity forgotten *)

    # Bunge layer: CES triple ⟨C, E, S⟩ *)
    System             # A ConcreteSystem / MobusSystem instance *)
    Component          # Member of C (composition). Disjoint from EnvObject by type separation. *)
    EnvObject          # Member of E.objects (environment). Disjoint from Component by type separation. *)

    # Mobus layer: elaborations beyond Bunge *)
    FlowEdge           # Edge in N (internal) or G (external) — FlowEdge α κ in Lean *)
    Boundary           # B = ⟨P, I⟩ — MobusBoundary α π *)
    Interface          # I ⊆ C — boundary interface components *)
    MilieuVar          # Member of M — ambient environmental variables (lost in Mobus→Bunge bridge) *)

  foreign_keys
    # --- Relation endpoints (Klir R ⊆ T × T) --- *)
    rel_source : Relation -> Thing
    rel_target : Relation -> Thing

    # --- Component and EnvObject are both Things --- *)
    comp_thing : Component -> Thing
    env_thing  : EnvObject -> Thing

    # --- System membership --- *)
    comp_system : Component -> System
    env_system  : EnvObject -> System

    # --- FlowEdge structure (FlowNetwork.lean: FlowEdge α κ) ---
       edge_source/edge_target point to Things (could be components or env objects).
       edge_system tracks which system's network this edge belongs to. *)
    edge_source : FlowEdge -> Thing
    edge_target : FlowEdge -> Thing
    edge_system : FlowEdge -> System

    # --- Interface ⊆ Component (Lean: interfaces_sub) --- *)
    iface_component : Interface -> Component
    iface_boundary  : Interface -> Boundary

    # --- Boundary belongs to system --- *)
    boundary_system : Boundary -> System

    # --- Milieu belongs to system (lost in toBunge projection) --- *)
    milieu_system : MilieuVar -> System

  # Path equations would go here for constraints like:
     edge_source.comp_thing = edge_source (if edges only connect components).
     However, CQL path equations require paths between the same two entity types,
     and our edges can connect both Components and EnvObjects (via Thing).
     The bipartite and network_components constraints are verified at the
     instance level rather than as schema-level path equations. *)

  attributes
    # Thing attributes *)
    thing_name  : Thing -> Str
    thing_label : Thing -> Str

    # System attributes *)
    system_name  : System -> Str
    system_level : System -> Int    # Mobus level index l in S_{i,l} *)

    # FlowEdge attributes *)
    edge_capacity : FlowEdge -> Dbl   # Mobus capacity κ — parametric in Lean *)
    edge_type     : FlowEdge -> Str   # "internal" (N) | "external" (G) *)
    edge_label    : FlowEdge -> Str

    # Boundary attributes *)
    boundary_props : Boundary -> Str  # π — serialized; Mobus: "exact form is research" *)

    # Milieu attributes (E.M — ambient variables) *)
    milieu_name  : MilieuVar -> Str
    milieu_value : MilieuVar -> Str

    # Relation attributes (for provenance) *)
    rel_label : Relation -> Str
}
