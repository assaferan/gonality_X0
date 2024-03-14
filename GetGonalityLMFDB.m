// Usage: ls input_data | parallel -j80 --timeout 600 "magma -b label:={1} GetGonalityLMFDB.m >> stdout/{1} 2>&1"
// where input_data is a folder containing one file for each label, consisting of data downloaded from the db using create_input_data.py

AttachSpec("gonality.spec");
SetColumns(0);
if assigned verbose or assigned debug then
    SetVerbose("ModularGonality", 1);
end if;
if assigned debug then
    SetDebugOnError(true);
end if;
if (not assigned label) then
    printf "This script assumes that label, the label of the X_H to compute, is given as a command line paramter.\n";
    printf "Something like magma label:=7.168.3.1 GetGonalityLMFDB.m\n";
    quit;
end if;

GonalityBounds(label);

exit;
