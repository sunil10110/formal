% Matlab script to take in z3 tseitin tactic output and convert to CNF

fname = 'C:\Users\XXX\OneDrive - NVIDIA Corporation\Documents (1)\ga10x\bringup\mta_all_cnf_hdcheck_030124.txt';
fid = fopen(fname);
M = [];
fid1 = fopen('C:\Dell\mta_all_cnf_hdcheck_030124_v2.cnf','w');

numlines = str2num( perl('countlines.pl', fname) );
disp(strcat('there are ', num2str(numlines), ' lines'));



lines = cell(numlines, 1);
clauses = cell(numlines, 1);

% Read lines into cell array
for i = 1:numlines
    lines{i} = fgetl(fid);
end

node_ctr = 0;
clause_ctr = 0;
i = 0;
flag_multi = 0;


h= waitbar(0,'reading file');



line_ctr = 0;

while line_ctr < numlines
    %disp(tline)
    line_ctr = line_ctr + 1;
    tline = lines{line_ctr};
    i = i+1;

    multi_line = 1; left_par = 0; right_par = 0;

    i_cur = i;
    while multi_line == 1        
        left_par = count(tline,"(");
        right_par =count(tline,")");
        
        if(left_par == right_par)
            multi_line = 0;
        else
            line_ctr = line_ctr + 1;
            tline = strcat(tline, " ",lines{line_ctr});
            i = i+1;
        end

    end

    if(i > i_cur)
        flag_multi = 1;
    else
        flag_multi = 0;
    end

    elems = strtrim(regexp(tline,'[(,)]','split'));
    str_ctr = 1;
    loc_elem_ctr = 0;
    clause = '';
    while str_ctr <= length(elems)
        flag_not = 0;    
        %if(isempty(M))
        if(isempty(elems{str_ctr}) || strcmp(elems{str_ctr},'Or'))
            str_ctr = str_ctr+1;
            continue;
        elseif(strcmp(strtrim(elems{str_ctr}),'Not'))
            % combine with next element
            %if(~contains(elems{str_ctr+1},'k!') || flag_multi == 0)
            %    flag_not = 1;
            %end
          
            flag_not = 1;
            str_ctr = str_ctr+1;
        end    
        loc_elem_ctr = loc_elem_ctr+1;
        if(isempty(M))
            % first creation
            node_ctr = node_ctr + 1;
            M = containers.Map(elems{str_ctr},node_ctr);
        elseif(~isKey(M,elems{str_ctr}))
            node_ctr = node_ctr + 1;
            M(elems{str_ctr}) = node_ctr;
        end
        if(flag_not)
            clause{loc_elem_ctr} = strcat('-',num2str(M(elems{str_ctr})));
        else
            clause{loc_elem_ctr} = num2str(M(elems{str_ctr}));
        end
        str_ctr = str_ctr + 1;        
    end

    % now display CNF string
    clause{length(clause)+1} = '0';
    fprintf(fid1,'%s ',clause{:});
    fprintf(fid1,'%s\n','');    
    clause_ctr = clause_ctr+1;
    line_ctr = line_ctr+1;
    %tline = fgetl(fid);
    tline = lines{line_ctr};
    if(mod(i,1000)==0)
        waitbar(i/numlines,h);
    end
end

fclose(fid);
fclose(fid1);
disp(clause_ctr)
disp(node_ctr)
