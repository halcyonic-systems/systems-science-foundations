#
   civic_to_cesm.cql
   Schema Mapping (Functor) F : GovGraph → CESM

   This is the core intellectual work: declaring what each civic data entity
   IS in systems-theoretic terms. The mapping is a functor between categories
   (presented as CQL schemas). CQL verifies it preserves all path structure.

   Key semantic interpretations:
     Entity      → Component    (government bodies are system components)
     Person      → Thing        (people are atomic things occupying roles)
     Meeting     → FlowEdge     (meetings are information/decision flows)
     Motion      → Relation     (motions are acts-on: mover acts on system state)
     BudgetItem  → FlowEdge     (budget allocations are resource flows)
     Document    → Thing        (documents are information artifacts)

   The Botetourt County system as a MobusSystem:
     C  = all 24 entities (Board, departments, commissions)
     N  = meetings between entities, budget flows between departments
     E  = citizens, state/federal gov (not yet in DB — Phase 1+)
     G  = tax revenue in, services out (budget_items with external parties)
     B  = county boundary; interfaces = elected officials (public-facing)
     T  = ordinance-making, budget approval processes
     H  = meeting minutes, document archive
     Δt = fiscal year / meeting schedule cadence
*)

# Import both schemas in a single file for CQL IDE *)

typeside Ty = literal {
  java_types
    Str = "java.lang.String"
    Int = "java.lang.Integer"
    Dbl = "java.lang.Double"
  java_fns
    concat : Str, Str -> Str = "(x, y) -> x + y"
    intToStr : Int -> Str = "(x) -> x.toString()"
    dblToStr : Dbl -> Str = "(x) -> x.toString()"
  java_constants
    zero : Int = "0"
    zeroDbl : Dbl = "0.0"
    empty : Str = "\"\""
    internal : Str = "\"internal\""
    external : Str = "\"external\""
    act : Str = "\"act\""
}

schema GovGraph = literal : Ty {
  entities
    Entity Person Meeting Document Motion BudgetItem
  foreign_keys
    person_entity  : Person -> Entity
    meeting_entity : Meeting -> Entity
    doc_meeting    : Document -> Meeting
    doc_entity     : Document -> Entity
    motion_meeting : Motion -> Meeting
    budget_entity  : BudgetItem -> Entity
    budget_meeting : BudgetItem -> Meeting
    entity_parent  : Entity -> Entity
  attributes
    entity_id    : Entity -> Str
    entity_name  : Entity -> Str
    entity_type  : Entity -> Str
    entity_desc  : Entity -> Str
    person_name  : Person -> Str
    person_role  : Person -> Str
    person_dist  : Person -> Str
    meeting_date : Meeting -> Str
    meeting_type : Meeting -> Str
    meeting_loc  : Meeting -> Str
    doc_type     : Document -> Str
    doc_title    : Document -> Str
    motion_text     : Motion -> Str
    motion_mover    : Motion -> Str
    motion_seconder : Motion -> Str
    motion_outcome  : Motion -> Str
    motion_yes      : Motion -> Int
    motion_no       : Motion -> Int
    budget_fy     : BudgetItem -> Str
    budget_desc   : BudgetItem -> Str
    budget_cat    : BudgetItem -> Str
    budget_amount : BudgetItem -> Dbl
}

schema CESM = literal : Ty {
  entities
    Thing Relation System Component EnvObject
    FlowEdge Boundary Interface MilieuVar
  foreign_keys
    rel_source      : Relation -> Thing
    rel_target      : Relation -> Thing
    comp_thing      : Component -> Thing
    env_thing       : EnvObject -> Thing
    comp_system     : Component -> System
    env_system      : EnvObject -> System
    edge_source     : FlowEdge -> Thing
    edge_target     : FlowEdge -> Thing
    edge_system     : FlowEdge -> System
    iface_component : Interface -> Component
    iface_boundary  : Interface -> Boundary
    boundary_system : Boundary -> System
    milieu_system   : MilieuVar -> System
  attributes
    thing_name     : Thing -> Str
    thing_label    : Thing -> Str
    system_name    : System -> Str
    system_level   : System -> Int
    edge_capacity  : FlowEdge -> Dbl
    edge_type      : FlowEdge -> Str
    edge_label     : FlowEdge -> Str
    boundary_props : Boundary -> Str
    milieu_name    : MilieuVar -> Str
    milieu_value   : MilieuVar -> Str
    rel_label      : Relation -> Str
}

# === The Mapping (Functor) === *)

mapping CivicToCESM = literal : GovGraph -> CESM {

  entity

    # Government entities are Components of the county system *)
    Entity -> Component

    # People are Things — they occupy roles but are not system components *)
    Person -> Thing

    # Meetings are FlowEdges — information/decision flows in the internal network *)
    Meeting -> FlowEdge

    # Documents are Things — information artifacts *)
    Document -> Thing

    # Motions are Relations — the mover acts-on the system state *)
    Motion -> Relation

    # Budget items are FlowEdges — resource flows with capacity = dollar amount *)
    BudgetItem -> FlowEdge

  foreign_keys

    # Person's entity → Component's underlying Thing
       A person serving in an entity maps to the thing underlying that component *)
    person_entity -> comp_thing

    # Meeting's entity → FlowEdge's system
       The entity hosting the meeting is the system the edge belongs to *)
    meeting_entity -> edge_system . comp_system

    # Document's meeting → the edge source's Thing
       (Document connects to the meeting's flow — maps to the Thing at the source) *)
    doc_meeting -> edge_source

    # Document's entity → Component's Thing *)
    doc_entity -> comp_thing

    # Motion's meeting → Relation source = meeting's flow source (the Thing that acts)
       A motion at a meeting: the relation source is the meeting's edge source *)
    motion_meeting -> rel_source . edge_source

    # Budget entity → FlowEdge system (the entity receiving the allocation) *)
    budget_entity -> edge_system . comp_system

    # Budget meeting → FlowEdge source (the meeting where budget was discussed) *)
    budget_meeting -> edge_source . edge_source

    # Entity parent → Component's system (parent entity = the system containing this component) *)
    entity_parent -> comp_system

  attributes

    # Entity attributes map through Component → Thing *)
    entity_id   -> thing_label . comp_thing
    entity_name -> thing_name . comp_thing
    entity_type -> lambda x. entity_type(x)
    entity_desc -> lambda x. entity_desc(x)

    # Person attributes map directly to Thing *)
    person_name -> thing_name
    person_role -> thing_label
    person_dist -> lambda x. person_dist(x)

    # Meeting attributes map to FlowEdge *)
    meeting_date -> edge_label
    meeting_type -> edge_type
    meeting_loc  -> lambda x. meeting_loc(x)

    # Document attributes map to Thing *)
    doc_type  -> thing_label
    doc_title -> thing_name

    # Motion attributes map to Relation *)
    motion_text     -> rel_label
    motion_mover    -> lambda x. motion_mover(x)
    motion_seconder -> lambda x. motion_seconder(x)
    motion_outcome  -> lambda x. motion_outcome(x)
    motion_yes      -> lambda x. motion_yes(x)
    motion_no       -> lambda x. motion_no(x)

    # Budget attributes map to FlowEdge *)
    budget_fy     -> edge_label
    budget_desc   -> lambda x. budget_desc(x)
    budget_cat    -> edge_type
    budget_amount -> edge_capacity
}
