package edu.umn.cs.crisys.smaccm.aadl2rtos.cli;

import java.io.File;
import java.util.List;
import java.util.Map;

import org.eclipse.core.runtime.IProgressMonitor;
import org.osate.aadl2.instance.SystemInstance;
import org.osate.aadl2.modelsupport.errorreporting.AnalysisErrorReporterManager;

import edu.umn.cs.crisys.smaccm.aadl2rtos.Aadl2RtosAction;
import edu.umn.cs.crisys.smaccm.aadl2rtos.ConsoleLogger;
import edu.umn.cs.crisys.smaccm.aadl2rtos.Logger;
import fr.tpt.aadl.ramses.control.support.analysis.AnalysisException;
import fr.tpt.aadl.ramses.control.support.config.RamsesConfiguration;
import fr.tpt.aadl.ramses.control.support.generator.GenerationException;
import fr.tpt.aadl.ramses.control.support.generator.Generator;
import fr.tpt.aadl.ramses.control.support.generator.TransformationException;
import fr.tpt.aadl.ramses.control.workflow.WorkflowPilot;

public class RtosGenerator implements Generator {

	private final String NAME = "rtos";
	
	@Override
	public String getRegistryName() {
		return NAME;
	}

	@Override
	public String getPluginName() {
		return NAME;
	}

	@Override
	public String getPluginId() {
		return NAME;
	}

	@Override
	public void generate(SystemInstance systemInstance,
			RamsesConfiguration config, File[] includeDirs,
			AnalysisErrorReporterManager errManager, IProgressMonitor monitor)
			throws AnalysisException, GenerationException,
			TransformationException {
		// TODO Auto-generated method stub
	
		(new Aadl2RtosAction()).execute(systemInstance, 
				systemInstance.getSystemImplementation(), monitor, 
				config.getRamsesOutputDir(), new ConsoleLogger(Logger.INFO));
	}

	@Override
	public void generateWorkflow(SystemInstance systemInstance,
			RamsesConfiguration config, WorkflowPilot xmlPilot,
			File[] includeDirs, AnalysisErrorReporterManager errManager,
			IProgressMonitor monitor) throws AnalysisException,
			GenerationException, TransformationException {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("workflow");
	}

	@Override
	public boolean runtimePathChecker(File runtimePath) {
		return true;
//		throw new UnsupportedOperationException("path check");
	}

	@Override
	public String getRuntimePathEnvVar() {
		return null;
		// throw new UnsupportedOperationException("env var");	
	}

	@Override
	public List<String> getTransformationModuleList() {
		throw new UnsupportedOperationException("trans list");	
	}

	@Override
	public List<String> getValidationModuleList() {
		throw new UnsupportedOperationException("val list");	
	}

	@Override
	public void setParameters(Map<String, Object> parameters) {
		return;
//		throw new UnsupportedOperationException("set param");
	}

}
