package com.rockwellcollins.atc.agree.analysis;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import jkind.api.results.MapRenaming;
import jkind.api.results.Renaming;
import jkind.lustre.Node;
import jkind.lustre.Program;
import jkind.results.layout.Layout;

import org.eclipse.emf.ecore.EObject;
import org.osate.aadl2.AnnexSubclause;
import org.osate.aadl2.ComponentImplementation;
import org.osate.aadl2.ComponentType;
import org.osate.aadl2.DataSubcomponent;
import org.osate.aadl2.Subcomponent;
import org.osate.aadl2.instance.ComponentInstance;

import com.rockwellcollins.atc.agree.agree.AgreeContractSubclause;

public class AgreeGenerator {
    
    private ComponentInstance compInst;
    private AgreeAnnexEmitter topEmitter;
    private String dotChar = "__";

    public AgreeGenerator(ComponentInstance compInst){
        this.compInst = compInst;
    }
    
    public Program evaluate(){
        
        ComponentImplementation compImpl = AgreeEmitterUtilities.getInstanceImplementation(compInst);
        ComponentType ct = AgreeEmitterUtilities.getInstanceType(compInst);
        AgreeLayout layout = new AgreeLayout();
        String category = "";
        
        AgreeAnnexEmitter topEmitter = new AgreeAnnexEmitter(
                compInst, layout, category, "", "", true, true);
        
        this.topEmitter = topEmitter;
        
        boolean foundAnnex = false;
        for (AnnexSubclause annex : compImpl.getAllAnnexSubclauses()) {
            if (annex instanceof AgreeContractSubclause) {
                topEmitter.doSwitch(annex);
                foundAnnex = true;
            }
        }

        
        
        for (AnnexSubclause annex : ct.getAllAnnexSubclauses()) {
            if (annex instanceof AgreeContractSubclause) {
                topEmitter.doSwitch(annex);
                foundAnnex = true;
            }
        }
        
        List<AgreeAnnexEmitter> subEmitters = new ArrayList<>();
        for(Subcomponent subComp : compImpl.getAllSubcomponents()){
        	//don't check data subcomponents
        	if(subComp instanceof DataSubcomponent){
        		continue;
        	}
        	
        	boolean foundSubAnnex = false;
            ComponentInstance subCompInst = compInst.findSubcomponentInstance(subComp);
            ct = AgreeEmitterUtilities.getInstanceType(subCompInst);
            ComponentImplementation subCompImpl = AgreeEmitterUtilities.getInstanceImplementation(subCompInst);
            category = subCompInst.getQualifiedName();
            AgreeAnnexEmitter subEmitter = new AgreeAnnexEmitter(
                    subCompInst, layout, category,
                    subCompInst.getName() + dotChar,
                    subCompInst.getName() + ".", false, false);

            if(subCompImpl != null){
                for (AnnexSubclause annex : subCompImpl.getAllAnnexSubclauses()) {
                    if (annex instanceof AgreeContractSubclause) {
                        subEmitter.doSwitch(annex);
                        foundSubAnnex = foundAnnex = true;
                    }
                }
            }

            for (AnnexSubclause annex : ct.getAllAnnexSubclauses()) {
                if (annex instanceof AgreeContractSubclause) {
                    subEmitter.doSwitch(annex);
                    foundSubAnnex = foundAnnex = true;
                }
            }

            if(foundSubAnnex){
            	subEmitters.add(subEmitter);
            }

        }
        if(!foundAnnex){
        	return null;
        }
        
        List<Node> nodes = topEmitter.getLustreWithCondacts(subEmitters);
        //List<Node> nodes = topEmitter.getLustre(subEmitters);

        return new Program(nodes);

    }

    public Map<String, EObject> getReferenceMap() {
        return topEmitter.refMap;
    }

    public Renaming getRenaming() {
        return new MapRenaming(topEmitter.varRenaming, MapRenaming.Mode.NULL);
    }

    public Layout getLayout() {
        return topEmitter.layout;
    }

    public String getLog() {
        return topEmitter.log.toString();
    }

    public List<String> getAssumeProps() {
        return topEmitter.assumProps;
    }

    public List<String> getConsistProps() {
        return topEmitter.consistProps;
    }

    public List<String> getGuarProps() {
        return topEmitter.guarProps;
    }


}
