# Revising and extending the mathematical framework for defining a system

## George E. Mobus

In Mobus, 2022, chapter 4, a mathematized framework for defining a general system was advanced and used to formulate a procedure for decomposing a system of interest (i.e., a particular kind of system) into its subsystems, their interactions with one another, and recursively down to its atomic components (those not needing further decomposition). That formulation, however, treated a system as being essentially static over its duration. That is, the system would not change over its life time. Additionally, the formulation only minimally represented the environment of a system. In this paper we seek to revise the model to enhance the handling of environmental aspects and to extend the model’s ability to represent a full life-cycle of any instance of any kind of system.

## Extending and Modifying the Framework

We begin with a basic revision of the original 7-tuple structure, reproduced here.

###### *Si,l=〈C,N,G,B,T,H,∆t〉i,l*      The original Eq. 4.1 in (Mobus, 2022).

Revised Eq. 4.1 is as follows.

###### *Si,l=〈C,N,E,G,B,T,H,∆t〉i,l*                                                                              (1)

In what follows, the subscript indexes, *i*, for index number in the set, and *l*, for level in the complexity/organization hierarchy will be dropped for simplicity.

*S* is now given as an oct-tuple with new member *E* containing the set, *O*, (standing for “objects” in the environment that are sources and sinks in a unified set) and a new object, *M*, containing the non-point source/sink variables constituting the interacting milieu around the system. Examples of a milieu are given below. The set *O* subsumes the sets, *Src* and *Snk* which were included in the original *G* bipartite network and were effectively ‘hidden’ from exposure of the model. This was deemed an unnecessary complexity, particularly since many objects in a system’s environment may be both sources and sinks simultaneously (for background, refer to Mobus, 2022). The environment object is now defined as:

E= 〈O,M〉   

O= 〈o0,o1,o2,…ok,…om〉   

Where *O* is the set of object sources and sinks in the environment of the SOI.

The milieu is represented by the abstract *M* object. *M* is the set of variables that are part of the environment but do not have a discrete (point) source. They surround or ‘bathe’ the system in conditions that impact or influence the state of the system, but do not interact necessarily through a discrete set of interfaces, as in the case of flows.

For example, *M* for a biological system might be as follows:

M=〈Temp,Humidity,Salinity,pH,Pressure〉 

We view this aspect of the environment and its interactions with the system an area for much more research, but are satisfied that the physical environments that are found in nature will provide real flesh to these abstract bones.

Given that the environment object now contains the set *O* as a unified set of environmental objects that interact with the system, we can proceed to simplify the *G* network, reducing it from a bipartite graph as in (Mobus, 2022\) to a more general graph. In the former there were two identified sets, as mentioned above. Thus, there were effectively three sets of nodes effectuating the need for a tri-partite graph. However, we note that many objects in the environment may be both sources, of flows, and sinks, receiving flows and would therefore need to be members of both sets. By reducing the two sets of environmental objects into a single set we obtain a simple graph with the flow directions (arrows) determining if an object is just a source or a sink or both. This will likely require changes to the knowledgebase schema as given in (Mobus, 2022, Chapter 8). That will be the subject for subsequent research. Edges in the G network now take this form:

###### *G= 〈oiO, cj∈C〉* 

The object, *oi*, is one of the point source or sink entities in the system environment, as noted above. The object, *cj*, is an element of the set of components in *C* that are identified as interfaces (with the environment) or the components that transport flows across the boundary. Such components are identified in the set *I* in the boundary object as in the original structure in (Mobus, 2022).

*(Figure 1: diagram showing E (environment) element implementation in S (SOI), with high power source object as both source and sink)*

**Fig. 1\.** Showing the implementation of the E (environment) element in S (SOI). Note that the high power source object shows a typical case where the object is both a source (for power and messages) and a sink (for messages).

## The System Life Cycle

The main objective of (Mobus, 2022\) was to provide a formal framework that would work to define a system by virtue of the structures and functions, their relations, and the hierarchical modular organization that characterizes real systems, both physical and abstract. However, that treatment ignored a critical aspect of real systems, namely that they age and change; they have a life cycle. Here we introduce the start of research into the characterization of system life cycles starting with the structure of equation (1) above. In what follows we take the time increment, Δ*t*, to be the eighth element in that equation, so it will be assumed below.

To formalize the notion of a system aging we consider a time series of system states and possible changes in those states. For example, the system *S* in the next time increment is the system *S* in the current state union some new (changed) state in one or more of the elements in *S*.

St+1=St〈∆S〉 

Where: the change in S can be any change in any of its elements.

∆S=〈∆C,∆N,∆E,∆G,∆B,∆T,∆H〉  

Here we provide several examples of what we mean. 

A change in the component set, C, could arise from the addition of a new component to the set, a deletion of a component, of simply a modification of the component (or combinations of these and affecting multiple components). Adding a new component is formally:

∆C=〈C∪cnew〉  

Similarly, adding a new link/connection between internal components produces a changed *N* set of edges:

∆N=〈Nci,cjnew〉  

As with the component set, we could also define deletions. Modification of an edge (say in a flow network) requires changing the label data, for example, changing a flow capacity which, in its present form, would require annotation in the knowledgebase.

∆E=〈E∆O〉  

∆O=〈Oonew〉


∆G=〈Gonew,ci〉


In other words, a change in *S* can involve changes in any of the component elements. Note that changes in *C* automatically imply changes in *N*, though not reciprocal. Changes in *C* include additions of new elements in *C*, i.e., new *cij*, deletion of some *cij*, or modifications of a *cij* = *Sij such as a material change in the transformation function, T.*

This represents a modification of the boundary object where an existing interface is removed and replaced with a new one. Such changes might occur when a system evolves its interaction points with the environment, such as when an organization replaces one type of customer interface with another.

∆B = ⟨B \\ {bk}, B ∪ {bnew}⟩

This represents the addition of a new transformation function to the system while preserving existing functions. This models how systems acquire new capabilities while maintaining their current functionality, as when an organization adds a new process or a software system implements a new feature."

∆T = ⟨T ∪ {tnew}⟩

### Stages of a Life Cycle

#### *Origination*
[Content pending from Mobus]

#### *Development*
[Content pending from Mobus]

#### *Maturation and Stable Operation*
[Content pending from Mobus]

#### *Decline*
[Content pending from Mobus]

#### *Dissolution*
[Content pending from Mobus]

## Discussion
[Content pending from Mobus]
