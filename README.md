__IMPORTANT NOTE__
________________________________________________________________________________________________________________________________________________________

The SAT-Framework in this project was designed by Manfred Scheucher (and Helena Bergold?)  
Link to the original project which is cloned: https://github.com/manfredscheucher/rotsys-sat/tree/main    
All Credit regarding the creation of this framework belongs to him (and her?).    
________________________________________________________________________________________________________________________________________________________
________________________________________________________________________________________________________________________________________________________

I used this Framework to study properties of almost complete graphs (complete graphs missing a (perfect) matching) for my bachelor thesis  
For this is extended the framework by creating additional parameters.  
The diffrence between this project and the  one on Manfreds Scheucher GitHub is that I added additional Parameters to rotsys.py  
So what did I do exactly:  
I cloned his project and added rotsys-extension.py - an extension of his version rotsys.py.  
For transparency I left the original rotsys.py.  
I did this so I could link the project in my thesis and in case someone is intrested in the additonal parameters.  

________________________________________________________________________________________________________________________________________________________

The following parameters have been added by me (version from 1.9.2025)

--fixMUp       : Given a matching (I)  and a upper bound (U) for crossing -> With this you can search for a Kn-I with cr(Kn-I) <= U  
--fixmLow       : Given a matching (I)  and a upper bound (L) for crossing -> With this you can search for a Kn-I with cr(Kn-I) >= L  
--twoColor      : Parameter with can be used to allow 2-color-crossings (disabled by default)  

--goodOcta      : Given a lower bound (L) -> This ensures there are atleast L crossings in all induced octahedrons default value is 1   
--octaFix       : Given a value (k)       -> This ensures there is at least one induced octahedron with k crossings  
--goodCross     : Given a value (k)       -> This ensures there are at least k good (4-color) crossings when you connect a Kn - I with an apex vertex. I is a perfect matching  


_______________________________________________________________________________________________________________________________________________________

THe parameters -fixMUp, -fixMLow, -twoColor are for complete graphs missing a matching quiet usefull.
The parameter -goodOcta, -octaFix, -goodCross were designed for a very specific use and might not be usefull for others
In all my code I tried to use Manfred Scheuchers style. I am sure there are parts which can be made "more optimal"
________________________________________________________________________________________________________________________________________________________

