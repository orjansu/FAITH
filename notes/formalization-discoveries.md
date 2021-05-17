
--Case study 1
I thought that the last step in case study 1 was -@-rules-1, but since the tool checked and saw that the side conditions didn't hold, I realized it was -@-rules-2.
I realized that I had the wrong context, and the discovery was when I checked where the callstack called. Add a log there perhaps?
you kinda don't check the side conditions.

Beviset tar inte bort den tomma dummy reference-variabeln vid reduktionen. -dummy-reference-algebra-5 måste läggas till.

--Case study 2
many let's in the beginning... Remove sometimes? Använd ngn funktion för att automatiskt ta fram skilnaden mellan två termers string-representation.

Hittade en bugg i systemet (glömt rekursivt call)
Insåg att man kan råka göra bort sig om man har fler än 1 $
Hittade en till bugg (glömt kolla substitutionerna inför side conditions)
kanske jag ska ha (a:as) som tillåten syntax för en cons...

om man ska vara noga så är dummy reference algebra-steget tre applikationer av dummy reference algebra (7,3,5,3,5)

jag gör felet med =[.] flera ggr, men jag kan inte ändra från x "=["v,w"]=" V
till x "=" "["v,w"]=" V utan att introducera en shift/reduce konflikt, och jag orkar inte fixa den just nu. Notera iaf detta i användarmanualen.

detta bevis skippade också att ta bort {}d^ efter reduktion.

när man inte säger ngt menar man nog -lr. Jag knsk ska ta bort den och lägga
till den automatiskt eller ngt.

FRÅGOR
det rekursiva har vanliga any i det rekursiva anropet. Är det meningen? - nej, det är ett fel i tesen.

Hur gör man för att få 0 heap weight? - om det är en top level definition som allokeras högst en gång, t.ex. library definitions.

hur ser anya' ut? - any, fast med <> på applikationerna


TODO
-Just nu så ser den till att variabler är skilda när den substituerar in till bool-termerna. Den ska se till att det inte krockar när den substituterar till samma term, men när det är olika bool-termer, så ska det vara okej att variabelnamn krockar. Annars blir det konstigt med substitutionen - eventuellt. Just nu funkar det...

After putting up the general things, I would like to let FAITH run through it to make sure that everything parses etc. It's not too hard, but requires some time. - delvis löst av $

Kontexter med flera hål stöds, men jag har inte använt dem än.
