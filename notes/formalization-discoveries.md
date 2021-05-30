
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

I och med att inlining inte har ngn space equvalence när funktionen inte är rekursiv, verkar det som att jag inte kan inline:a false till False när allting är klart. Därför verkar det som att beviset hänger delvis på att false=False är en top-level definition som därmed kan ha 0 i hw och sw. Altså måste jag lägga till false =[0,0]= False som en top-level definition för att allt ska funka. Intressant är i alla fall att jag försökte göra detta och FAITH sa emot.

Jag insåg att jag hade en lite annan version av any_a eftersom jag
faktiskt hade följt den desugarade versionen av any_a istället för den som blir om man använder den sugarade versionen och hur man unsugarrar den till punkt och pricka. Dvs
jag använde
`let { z = @
     , a = p <> y
     , b = {z}d^(any_a <> p <> ys)}
in or <> a <> b`
medans Gustavsson och Sands sa att de använde den övre, men när de kommer till den i post-induktion-steget av beviset, använder de
`let { z = @ }
in or <> (p <> y) <> {z}d^(any_a <> p <> ys)`
vilket om man mekaniskt unsugarar det blir
`let { z = @}
 in let {ds = {z}d^(any_a <> p <> bs)}
    in (let {c = p <> b}
        in or <> c) <> ds)`

-Det är rätt störigt att man måste ändra överallt på orelaterade grejer om man vill gå tillbaka i beviset. Med matching och pretty-printing skulle detta lösas.
-Det skulle vara coolt om man kunde referera till andra substitutioner när man specificerar dem, men ev bara nödvändigt vid reduction.
-skulle vara najs att printa sideconditions, men man kan istället bara kommentera ut dem i lagfilen

jag trodde ett tag att jag skulle behöva en regel
`(\ a. \b. M) x y <~> s^((\a. (\b. M) x) y)`
men insåg först att det var fel, att jag menade
`(\ a. \b. M) y x <~> s^((\a. (\b. M) x) y)`
och sen att man kan ta sig mellan dem mha reduction osv.

FRÅGOR
det rekursiva har vanliga any i det rekursiva anropet. Är det meningen? - nej, det är ett fel i tesen.

Hur gör man för att få 0 heap weight? - om det är en top level definition som allokeras högst en gång, t.ex. library definitions.

hur ser anya' ut? - any, fast med <> på applikationerna


TODO
-Just nu så ser den till att variabler är skilda när den substituerar in till bool-termerna. Den ska se till att det inte krockar när den substituterar till samma term, men när det är olika bool-termer, så ska det vara okej att variabelnamn krockar. Annars blir det konstigt med substitutionen - eventuellt. Just nu funkar det...

After putting up the general things, I would like to let FAITH run through it to make sure that everything parses etc. It's not too hard, but requires some time. - delvis löst av $

Kontexter med flera hål stöds, men jag har inte använt dem än.
