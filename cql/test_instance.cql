options
  timeout = 300

# test_instance.cql — CESM Ontology + Gov Graph + Mapping + Test Data

typeside Ty = literal {
  imports
    sql
}

schema GovGraph = literal : Ty {
  entities
    Entity Person Meeting Document Motion BudgetItem
  foreign_keys
    person_entity  : Person -> Entity
    meeting_entity : Meeting -> Entity
    doc_meeting    : Document -> Meeting
    motion_meeting : Motion -> Meeting
    budget_entity  : BudgetItem -> Entity
  attributes
    entity_id    : Entity -> Varchar
    entity_name  : Entity -> Varchar
    entity_type  : Entity -> Varchar
    entity_desc  : Entity -> Varchar
    person_name  : Person -> Varchar
    person_role  : Person -> Varchar
    person_dist  : Person -> Varchar
    meeting_date : Meeting -> Varchar
    meeting_type : Meeting -> Varchar
    meeting_loc  : Meeting -> Varchar
    doc_type     : Document -> Varchar
    doc_title    : Document -> Varchar
    motion_text     : Motion -> Varchar
    motion_mover    : Motion -> Varchar
    motion_seconder : Motion -> Varchar
    motion_outcome  : Motion -> Varchar
    motion_yes      : Motion -> Integer
    motion_no       : Motion -> Integer
    budget_fy     : BudgetItem -> Varchar
    budget_desc   : BudgetItem -> Varchar
    budget_cat    : BudgetItem -> Varchar
    budget_amount : BudgetItem -> Integer
}

schema CESM = literal : Ty {
  entities
    Thing Relation Sys Component EnvObject
    FlowEdge Boundary Interface MilieuVar
  foreign_keys
    rel_source      : Relation -> Thing
    rel_target      : Relation -> Thing
    rel_edge        : Relation -> FlowEdge
    comp_thing      : Component -> Thing
    comp_sys        : Component -> Sys
    env_thing       : EnvObject -> Thing
    env_sys         : EnvObject -> Sys
    edge_source     : FlowEdge -> Thing
    edge_target     : FlowEdge -> Thing
    edge_sys        : FlowEdge -> Sys
    edge_component  : FlowEdge -> Component
    iface_component : Interface -> Component
    iface_boundary  : Interface -> Boundary
    boundary_sys    : Boundary -> Sys
    milieu_sys      : MilieuVar -> Sys
  attributes
    thing_name     : Thing -> Varchar
    thing_label    : Thing -> Varchar
    thing_desc     : Thing -> Varchar
    thing_extra    : Thing -> Varchar
    sys_name       : Sys -> Varchar
    sys_level      : Sys -> Integer
    comp_type      : Component -> Varchar
    comp_desc      : Component -> Varchar
    edge_capacity  : FlowEdge -> Integer
    edge_type      : FlowEdge -> Varchar
    edge_label     : FlowEdge -> Varchar
    edge_loc       : FlowEdge -> Varchar
    edge_desc      : FlowEdge -> Varchar
    boundary_props : Boundary -> Varchar
    milieu_name    : MilieuVar -> Varchar
    milieu_value   : MilieuVar -> Varchar
    rel_label      : Relation -> Varchar
    rel_mover      : Relation -> Varchar
    rel_seconder   : Relation -> Varchar
    rel_outcome    : Relation -> Varchar
    rel_yes        : Relation -> Integer
    rel_no         : Relation -> Integer
}

# Functor F : GovGraph -> CESM

mapping CivicToCESM = literal : GovGraph -> CESM {
  entity
    Entity -> Component
  attributes
    entity_id   -> comp_thing . thing_label
    entity_name -> comp_thing . thing_name
    entity_type -> comp_type
    entity_desc -> comp_desc

  entity
    Person -> FlowEdge
  foreign_keys
    person_entity -> edge_component
  attributes
    person_name -> edge_label
    person_role -> edge_type
    person_dist -> edge_loc

  entity
    Meeting -> FlowEdge
  foreign_keys
    meeting_entity -> edge_component
  attributes
    meeting_date -> edge_label
    meeting_type -> edge_type
    meeting_loc  -> edge_loc

  entity
    Document -> Relation
  foreign_keys
    doc_meeting -> rel_edge
  attributes
    doc_type  -> rel_label
    doc_title -> rel_mover

  entity
    Motion -> Relation
  foreign_keys
    motion_meeting -> rel_edge
  attributes
    motion_text     -> rel_label
    motion_mover    -> rel_mover
    motion_seconder -> rel_seconder
    motion_outcome  -> rel_outcome
    motion_yes      -> rel_yes
    motion_no       -> rel_no

  entity
    BudgetItem -> FlowEdge
  foreign_keys
    budget_entity  -> edge_component
  attributes
    budget_fy     -> edge_label
    budget_desc   -> edge_desc
    budget_cat    -> edge_type
    budget_amount -> edge_capacity
}

# Test Instance

instance GovData = literal : GovGraph {
  generators
    county bos planning fire_dept : Entity
    scothorn nicely : Person
    jan_meeting feb_meeting : Meeting
    jan_agenda jan_minutes : Document
    approve_mins budget_amend : Motion
    fire_ops schools : BudgetItem

  equations
    entity_id(county) = "botetourt-county"
    entity_name(county) = "Botetourt County"
    entity_type(county) = "jurisdiction"
    entity_desc(county) = "County government Fincastle VA"

    entity_id(bos) = "board-of-supervisors"
    entity_name(bos) = "Board of Supervisors"
    entity_type(bos) = "elected"
    entity_desc(bos) = "Chief governing body"

    entity_id(planning) = "planning-commission"
    entity_name(planning) = "Planning Commission"
    entity_type(planning) = "board_commission"
    entity_desc(planning) = "Land use and zoning"

    entity_id(fire_dept) = "fire-ems"
    entity_name(fire_dept) = "Fire and EMS"
    entity_type(fire_dept) = "department"
    entity_desc(fire_dept) = "Emergency services"

    person_entity(scothorn) = bos
    person_name(scothorn) = "D Mac Scothorn"
    person_role(scothorn) = "Board Chair"
    person_dist(scothorn) = "Fincastle"

    person_entity(nicely) = bos
    person_name(nicely) = "Steve Nicely"
    person_role(nicely) = "Supervisor"
    person_dist(nicely) = "Amsterdam"

    meeting_entity(jan_meeting) = bos
    meeting_date(jan_meeting) = "2025-01-14"
    meeting_type(jan_meeting) = "regular"
    meeting_loc(jan_meeting) = "Fincastle Courthouse"

    meeting_entity(feb_meeting) = bos
    meeting_date(feb_meeting) = "2025-02-11"
    meeting_type(feb_meeting) = "regular"
    meeting_loc(feb_meeting) = "Fincastle Courthouse"

    doc_meeting(jan_agenda) = jan_meeting
    doc_type(jan_agenda) = "agenda"
    doc_title(jan_agenda) = "BOS Agenda January 14 2025"

    doc_meeting(jan_minutes) = jan_meeting
    doc_type(jan_minutes) = "minutes"
    doc_title(jan_minutes) = "BOS Minutes January 14 2025"

    motion_meeting(approve_mins) = jan_meeting
    motion_text(approve_mins) = "Approve minutes of December 17 2024"
    motion_mover(approve_mins) = "Scothorn"
    motion_seconder(approve_mins) = "Nicely"
    motion_outcome(approve_mins) = "passed"
    motion_yes(approve_mins) = 5
    motion_no(approve_mins) = 0

    motion_meeting(budget_amend) = feb_meeting
    motion_text(budget_amend) = "Approve FY2025 budget amendment"
    motion_mover(budget_amend) = "Nicely"
    motion_seconder(budget_amend) = "Scothorn"
    motion_outcome(budget_amend) = "passed"
    motion_yes(budget_amend) = 4
    motion_no(budget_amend) = 1

    budget_entity(fire_ops) = fire_dept
    budget_fy(fire_ops) = "FY2025"
    budget_desc(fire_ops) = "Fire and EMS Operations"
    budget_cat(fire_ops) = "expenditure"
    budget_amount(fire_ops) = 5200000

    budget_entity(schools) = bos
    budget_fy(schools) = "FY2025"
    budget_desc(schools) = "Public Schools Transfer"
    budget_cat(schools) = "expenditure"
    budget_amount(schools) = 18500000
}

# Sigma pushforward: civic data -> CESM shape
instance CESMData = sigma CivicToCESM GovData

# Export commands — run individually from the IDE
command exportCsv = export_csv_instance CESMData "./export"
command exportGovCsv = export_csv_instance GovData "./export_gov"
