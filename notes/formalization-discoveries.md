
--Case study 1
I thought that the last step in case study 1 was -@-rules-1, but since the tool checked and saw that the side conditions didn't hold, I realized it was -@-rules-2.
I realized that I had the wrong context, and the discovery was when I checked where the callstack called. Add a log there perhaps?
you kinda don't check the side conditions.

Beviset tar inte bort den tomma dummy reference-variabeln vid reduktionen. -dummy-reference-algebra-5 måste läggas till.

--Case study 2
many let's in the beginning... Remove sometimes? Använd ngn funktion för att automatiskt ta fram skilnaden mellan två termers string-representation.

Hittade en bugg i systemet.

FRÅGOR
det rekursiva har vanliga any i det rekursiva anropet. Är det meningen? - nej, det är ett fel i tesen.

Hur gör man för att få 0 heap weight? - om det är en top level definition som allokeras högst en gång, t.ex. library definitions.

hur ser anya' ut?


TODO
-Just nu så ser den till att variabler är skilda när den substituerar in till bool-termerna. Den ska se till att det inte krockar när den substituterar till samma term, men när det är olika bool-termer, så ska det vara okej att variabelnamn krockar. Annars blir det konstigt med substitutionen - eventuellt. Just nu funkar det...

After putting up the general things, I would like to let FAITH run through it to make sure that everything parses etc. It's not too hard, but requires some time.
