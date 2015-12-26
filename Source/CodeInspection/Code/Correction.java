    private Subject getSubjectFromSecurityCurrent() 
            throws SecurityMechanismException {
        com.sun.enterprise.security.SecurityContext securityContext;
        securityContext = com.sun.enterprise.security.SecurityContext.getCurrent();
        if(securityContext == null) {
            fineLevelLog(" SETTING GUEST ---");
            securityContext = com.sun.enterprise.security.SecurityContext.init();
        }
        if(securityContext == null) {
            throw new SecurityMechanismException("Could not find " +
                                                 "security information");
        }
        Subject subject = securityContext.getSubject();
        if(subject == null) {
            throw new SecurityMechanismException("Could not find " +
                                                 "subject information in the " +
                                                 "security context.");
        }
        fineLevelLog("Subject in security current:" + subject);
        return subject;
    }

    public CompoundSecMech selectSecurityMechanism(IOR ior) 
            throws SecurityMechanismException {
        CompoundSecMech[] mechList = getCtc().getSecurityMechanisms(ior);
        CompoundSecMech mech = selectSecurityMechanism(mechList);
        return mech;
    }

    /**
     * Select the security mechanism from the list of compound security
     * mechanisms.
     */
    private CompoundSecMech selectSecurityMechanism(CompoundSecMech[] mechList)
                                throws SecurityMechanismException {
        // We should choose from list of compound security mechanisms
        // which are in decreasing preference order. Right now we select
        // the first one.
        if(mechList == null || mechList.length == 0) {
            return null;
        }
        CompoundSecMech mech;
        for(int i = 0; i < mechList.length; i++) {
            mech = mechList[i];
            boolean useMech = useMechanism(mech);
            if(useMech) {
                return mech;
            }
        }
        throw new SecurityMechanismException("Cannot use any of the " +
                                             "target's supported mechanisms");
    }

    private boolean useMechanism(CompoundSecMech mech) {
        boolean val = true;
        TLS_SEC_TRANS tls = getCtc().getSSLInformation(mech);

        if (mech.sas_context_mech.supported_naming_mechanisms.length > 0 &&
            !isMechanismSupported(mech.sas_context_mech)) {
            return false;
        } else if (mech.as_context_mech.client_authentication_mech.length > 0 &&
                   !isMechanismSupportedAS(mech.as_context_mech)) {
            return false;
        }

        if(tls == null) {
            return true;
        }
        int targetRequires = tls.target_requires;
        if(isSet(targetRequires, EstablishTrustInClient.value)) {
            if(! sslUtils.isKeyAvailable()) {
                val = false;
            }
        }
        return val;
    }

    private boolean evaluateClientConformanceSsl(
                        EjbIORConfigurationDescriptor iordesc,
                        boolean  sslUsed,
                        X509Certificate[] certchain) {
        
        boolean sslRequired  = false;
        boolean sslSupported = false;
        int sslTargetRequires = 0;
        int sslTargetSupports = 0;
        
        try {
            fineLevelLog("SecurityMechanismSelector.evaluate_client_" +
                         "conformance_ssl->:");

            /*******************************************************************
             * Conformance Matrix:
             *
             * |---------------|-----------------|-----------------|-----------|
             * | SSLClientAuth | targetrequires. | targetSupports. | Conformant|
             * |               |       ETIC      |      ETIC       |           |
             * |---------------|-----------------|-----------------|-----------|
             * |     Yes       |          0      |      1          |    Yes    |
             * |     Yes       |          0      |      0          |    No     |
             * |     Yes       |          1      |      X          |    Yes    |
             * |     No        |          0      |      X          |    Yes    |
             * |     No        |          1      |      X          |    No     |
             * |---------------|-----------------|-----------------|-----------|
             *
             ******************************************************************/

            // gather the configured SSL security policies.

            sslTargetRequires = this.getCtc().getTargetRequires(iordesc);
            sslTargetSupports = this.getCtc().getTargetSupports(iordesc);

            if (isSet(sslTargetRequires, Integrity.value) ||
                isSet(sslTargetRequires, Confidentiality.value) ||
                isSet(sslTargetRequires, EstablishTrustInClient.value)) {
                sslRequired = true;
            } else {
                sslRequired = false;
            }

            if ( sslTargetSupports != 0) {
                sslSupported = true;
            } else {
                sslSupported = false;
            }

            /* Check for conformance for using SSL usage.
             * 
             * a. if SSL was used, then either the target must require or 
             *    support SSL. In the latter case, SSL is used because of client
             *    policy.
             * b. if SSL was not used, then the target must not require it 
             *    either. The target may or may not support SSL (it is 
             *    irrelevant).
             */
            fineLevelLog("SecurityMechanismSelector.evaluate_client_" +
                         "conformance_ssl:" +
                         " " + isSet(sslTargetRequires, Integrity.value) +
                         " " + isSet(sslTargetRequires, Confidentiality.value) +
                         " " + 
                         isSet(sslTargetRequires,EstablishTrustInClient.value) +
                         " " + sslRequired +
                         " " + sslSupported +
                         " " + sslUsed);

            if (sslUsed) {
                if (! (sslRequired || sslSupported)) {
                    return false;  // security mechanism did not match
                }
            } else {
                if (sslRequired) {
                    return false;  // security mechanism did not match
                }
            }

            /* Check for conformance for SSL client authentication.
             *
             * a. if client performed SSL client authentication, then the target
             *    must either require or support SSL client authentication. If 
             *    the target only supports, SSL client authentication is used
             *    because of client security policy.
             *
             * b. if SSL client authentication was not used, then the target must
             *    not require SSL client authentcation either. The target may or may 
             *    not support SSL client authentication (it is irrelevant).
             */

            fineLevelLog("SecurityMechanismSelector.evaluate_client_" +
                         "conformance_ssl:" +
                         " " + 
                         isSet(sslTargetRequires,EstablishTrustInClient.value) +
                         " " + 
                         isSet(sslTargetSupports,EstablishTrustInClient.value));

            if (certchain != null) {
                if ( ! ( isSet(sslTargetRequires, EstablishTrustInClient.value) ||
                     isSet(sslTargetSupports, EstablishTrustInClient.value))) {
                    return false; // security mechanism did not match
                }
            } else {
                if (isSet(sslTargetRequires, EstablishTrustInClient.value)) {
                    return false; // security mechanism did not match
                }
            }

            fineLevelLog("SecurityMechanismSelector.evaluate_client_" +
                         "conformance_ssl: true");

            return true ; // mechanism matched
        } finally {
            fineLevelLog("SecurityMechanismSelector.evaluate_client_" +
                         "conformance_ssl<-:");
        }
    }
    
    //At the end of the class or into a specific class dedicated to the logger
    private fineLevelLog (String s) {
        if(_logger.isLoggable(Level.FINE)) {
            _logger.log(Level.FINE, s);
        }
    }
    
