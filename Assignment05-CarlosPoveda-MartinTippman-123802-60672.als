
abstract sig Person {
	killed: set Person,
	hates: set Person,
	richer: set Person
}

one sig Agatha, Butler, Charles extends Person {}

fact {
	// There are only 3 people
	#Person = 3
	// Someone who lived in Dreadbury Mansion killed Aunt Agatha.
	 some killed.Agatha
	//A killer always hates his victim, and is never richer than his victim. 
	all p1, p2 : Person | p2 in p1.killed implies (p2 in p1.hates and p2 not in p1.richer)
	//Agatha hates everyone except the Butler.
	--Agatha.hates = (Person - Butler)
	all p : Person | p in Agatha.hates implies p not in Charles.hates
	//The Butler also hates everyone Agatha hates.
	--Butler.hates = Agatha.hates
	Agatha in Agatha.hates and Charles in Agatha.hates
	//Charles hates no one that aunt Agatha hates.
	all p : Person | Agatha not in p.richer implies p in Butler.hates
	//The Butler hates everyone not richer than Aunt Agatha.
	all p : Person | p in Agatha.hates implies p in Butler.hates
	//No one hates everyone.
	all p : Person | Person not in p.hates
}

run {one Person.killed}  for 3
